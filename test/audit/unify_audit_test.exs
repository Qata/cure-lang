defmodule Cure.Audit.UnifyTest do
  @moduledoc """
  Audit findings for `lib/cure/elab/unify.ex` (the elaborator's first-order
  metavariable unifier: solve/occurs-check/scope-check/Miller-pattern
  unification for constructor-argument and implicit-parameter inference).

  Scope note: this module is UNTRUSTED elaborator machinery, not the kernel's
  case-branch index unifier (`Cure.Core.Kernel.branch_unify/4`, which owns the
  Solution/Injectivity/Deletion/Clash/Cycle rules for `:impossible` verdicts —
  audited separately). Every term this file assembles is independently
  re-checked by the trusted kernel before it can affect a program's behavior,
  so most bugs here degrade to spurious elaboration errors rather than
  provable-False soundness holes. UN1 below is the exception: it is a missing
  SCOPE CHECK (the Miller-pattern "does the solution reference a variable out
  of the metavariable's scope?" question) that lets `solve/4` silently accept
  a malformed solution — `{:var, -1}`, a negative/dangling de Bruijn index —
  instead of rejecting it. That is squarely the class of bug this audit is
  chartered to find even though the immediate consequence in this codebase is
  most likely an elaborator crash reaching the kernel (not a proof of False):
  a scope check that quietly passes when it should reject is exactly the
  defect this audit is chartered to catch, and the failure mode of *silently
  wrong* variable capture (rather than a clean rejection) is the dangerous
  half of "conservative failure" the rest of this file (occurs?, the Miller
  vars_ok? check, strengthen's :escape path) is built around.

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{MetaCtx, Unify}

  # ---------------------------------------------------------------------
  # UN1: `strengthen/2` (unify.ex, solve's scope check) decides whether a
  # metavariable's proposed solution may be recorded at the metavariable's
  # ambient (depth-0) frame, by asking `escapes?/3`: "does this term
  # reference any of the `depth` binders being stripped away?" This is the
  # exact question the Miller-pattern literature calls the SCOPE CHECK — the
  # dual of the occurs check, and just as load-bearing: a `false` answer here
  # means `strengthen` proceeds to blindly subtract `depth` from every free
  # variable via `Cure.Elab.Subst.shift(t, -depth, 0)`.
  #
  # `escapes?/3` (unify.ex ~374-389) is a hand-rolled per-shape walk with
  # explicit clauses for `:var`, `:meta`, `:pi`, `:lam`, `:app`, `:data`,
  # `:ctor`, and a catch-all `escapes?(_other, _depth, _local), do: false`.
  # That catch-all is correct for every CURRENT Core leaf shape with no
  # sub-terms (`:type`, `:global`, `:int_lit`, `:nat_lit`, `:bounded_lit`,
  # `:float_lit`, `:int_type`, `:float_type`, `:binary_type`) — but `:case`
  # (`{:case, scrut, motive, branches}`, `lib/cure/core/term.ex` node
  # taxonomy) is NOT a leaf: its branch bodies bind `arity` extra variables
  # and routinely reference the very binders `escapes?` is being asked
  # about (a dependent Pi codomain matching on its own bound argument —
  # `(x: T) -> case x { C() -> x }` — is completely ordinary dependent-type
  # usage, not a contrived shape). Because `:case` falls through to the
  # `false` catch-all, `escapes?` always answers "no escape" for it,
  # regardless of what its branches actually reference.
  #
  # This is precisely the same defect class the project already found and
  # fixed elsewhere in this very file: `zonk/2`, `occurs?/3`, and
  # `meta_free?/1` all carry a comment ("Structurally complete: walk EVERY
  # subterm-bearing shape...") explaining that an earlier, shape-enumerated
  # version of each of them missed exactly this kind of node and let a bug
  # slip past (see `test/cure/elab/unify_meta_completeness_test.exs`, which
  # pins the fixed behavior for `zonk`/`meta_free?` against `:eq`/`:sigma`/
  # `:pair`/`:prim`). `escapes?` (and, not incidentally, `mabs/5`, the Miller
  # abstraction helper) were never migrated to that generic walk. `mabs`
  # happens to still enumerate every shape in the CURRENT grammar (it has an
  # explicit `:case` clause) so it is not at risk today, but `escapes?` is
  # missing exactly that one clause, live, right now.
  #
  # Concretely: unifying `(x: Type) -> ?m` against `(x: Type) -> case x { C() -> x }`
  # crosses the Pi binder (depth 1 while comparing codomains), so `?m` is
  # solved against a `:case` term whose sole branch body is `{:var, 0}` — a
  # reference to the very Pi binder just crossed, which unambiguously escapes
  # the metavariable's ambient scope and must be rejected. Instead:
  #   1. `escapes?(case_term, 1, 0)` hits the `:case`-less catch-all → `false`.
  #   2. `strengthen` proceeds: `Cure.Elab.Subst.shift(case_term, -1, 0)`
  #      turns the branch's `{:var, 0}` into `{:var, -1}` — Subst.shift IS
  #      structurally complete for `:case` (it has the explicit clause
  #      `escapes?` lacks), so it faithfully propagates the corruption rather
  #      than crashing.
  #   3. `solve_strengthened` records `?m := {:case, ..., [{:C, 0, {:var, -1}}]}`
  #      as a SUCCESSFUL solution — `unify/3` returns `{:ok, _}`, not the
  #      `{:error, {:escaping_variable, _}}` a correct scope check demands.
  #
  # A negative de Bruijn index is not an inert "will be caught by the kernel"
  # artifact the way an unsolved `{:meta, _}` is (that has a dedicated
  # `has_meta?`/`meta_free?` firewall right in this file): it is a
  # syntactically well-formed `{:var, k}` tuple that will keep flowing through
  # ordinary term machinery (shift/subst/zonk all happily process it further)
  # until something finally indexes an environment or telescope with it —
  # at best a crash, at worst (many list/environment lookups in this
  # codebase and its BEAM substrate accept negative indices as
  # "count from the end") a silent, wrong variable substitution with no
  # error at all. Reference: Agda's `checkMetaOccurs`/`PatternVar` machinery
  # and Idris 2's `Core/Unify.idr` `patternEnvironment` both fold the scope
  # check into the SAME generic-shape traversal used for occurs-check, for
  # exactly this reason — a hand-maintained enumeration silently rots as the
  # term grammar grows.
  test "UN1: solving a metavariable against a case-term that references a crossed binder is rejected (scope check), not silently accepted with a corrupted solution" do
    ctx = MetaCtx.new()
    {ctx, id} = MetaCtx.fresh(ctx)
    dom = {:type, 0}

    # (x: Type) -> case x { C() -> x }  — the branch body is the Pi's own
    # bound variable, `{:var, 0}`, referenced one binder inside the codomain.
    case_term = {:case, {:global, :dummy_scrutinee}, {:lam, dom, dom}, [{:C, 0, {:var, 0}}]}

    t1 = {:pi, dom, {:meta, id}}
    t2 = {:pi, dom, case_term}

    assert {:error, {:escaping_variable, ^id}} = Unify.unify(t1, t2, ctx)
  end

  # UN1b: the identical gap, reached through one more layer of structural
  # recursion — the case term sits inside a constructor argument rather than
  # directly as the codomain. `escapes?({:ctor, _c, args}, depth, local)`
  # itself is correct (it maps `escapes?/3` over `args`), but each recursive
  # call bottoms out in the same broken `:case` catch-all, so the corrupted
  # solution is reachable from any position `escapes?` is asked to check, not
  # just the toplevel codomain — e.g. a constructor whose argument type
  # mentions a `match` over an earlier telescope variable.
  test "UN1b: the same scope-check gap fires when the case term is nested inside a constructor argument" do
    ctx = MetaCtx.new()
    {ctx, id} = MetaCtx.fresh(ctx)
    dom = {:type, 0}

    case_term = {:case, {:global, :dummy_scrutinee}, {:lam, dom, dom}, [{:C, 0, {:var, 0}}]}

    t1 = {:pi, dom, {:meta, id}}
    t2 = {:pi, dom, {:ctor, :Wrap, [case_term]}}

    assert {:error, {:escaping_variable, ^id}} = Unify.unify(t1, t2, ctx)
  end
end
