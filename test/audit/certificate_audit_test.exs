defmodule Cure.Audit.CertificateTest do
  @moduledoc """
  Audit findings for `lib/cure/core/certificate.ex` (size-change termination,
  TCB). See the accompanying audit report for the full writeup; summary here.

  Root cause shared by T1 and T2: `calls?/2` (the self-call fast-path
  detector) and `walk`/`walk_node` (the change-matrix builder) are BOTH
  written as an exhaustive case-list over the Core term grammar, and their
  catch-all clauses FAIL OPEN:

      defp calls?(_name, _term), do: false
      defp walk_node(_emit, _term, _st, acc), do: acc

  An unrecognized tuple shape silently contributes "no call here" rather than
  "unknown, be conservative." This is the opposite convention from the rest
  of the same TCB directory:

    * `Cure.Core.Term.term?/1` catch-all: `def term?(_), do: false` (fail
      CLOSED -- unrecognized = invalid term).
    * `Cure.Core.Validator.children/1` fallback (validator.ex:140-153) is
      explicitly documented as fail-closed: "Descend CONSERVATIVELY into
      every element that is itself a term-tuple... so a forbidden node
      buried in an unknown wrapper cannot escape the walker (fail-closed)."

  `certificate.ex` has no analogous fallback, so a self-call nested inside
  any node shape it does not special-case (any 2+-tuple other than
  `:global`/`:pi`/`:lam`/`:app`/`:data`/`:ctor`/`:case`) is invisible to
  BOTH the fast path and the matrix builder.

  Today this is not reachable through the full `Kernel.validate_certificate`
  pipeline: `check_def` runs first, and the kernel's `infer`/`check` grammar
  is exhaustively closed over exactly {type, var, int_type, int_lit,
  nat_lit, bounded_lit, float_type, float_lit, binary_type, absurd, pi, lam,
  global, app, data, ctor, case, hole} (verified by reading every `infer`/
  `check` clause head in kernel.ex) -- a term containing any other tuple
  shape would raise a FunctionClauseError in `check`/`infer` before
  `Certificate.terminating?/3` is ever invoked with it. Historically-real
  grammar members that WOULD have hit this gap (`:eq`, `:refl`, `:rewrite`,
  `:sigma`, `:pair`, `:fst`, `:snd`, `:prim`) have all since been retired
  from the kernel (git log: 727a673, 11ea830, 9680229, and K2's prim removal)
  and have no producers left.

  But `Certificate.terminating?/3` is itself public and independently
  callable with no precondition that its `body` argument has already passed
  `check_def` -- exactly how `certify_hardening_test.exs` and
  `mutual_cycle_pending_cert_test.exs` already call it directly, and exactly
  how any future caller (a new tool, a refactor of `validate_certificate`,
  a not-yet-retired grammar member reintroduced by the identity-type-as-
  inductive work in flight) could call it too. The module's own moduledoc
  states unconditionally "the kernel never certifies a function it cannot
  prove total" -- T1 and T2 show that claim is false for
  `Certificate.terminating?/3` in isolation, via two independent code paths
  (the singleton self-recursion fast path, and the cross-function/mutual
  closure).

  Fix sketch (not applied by this audit): give `walk_node`'s catch-all (and
  `calls?`'s) the same fail-closed treatment as `Validator.children/1` --
  conservatively descend into every tuple/list element of an unrecognized
  node instead of returning the accumulator unchanged / `false`.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.{Certificate, Env}

  # T1: a self-call hidden inside an unrecognized wrapper node bypasses the
  # `calls?/2` fast path entirely, so `size_change_total?/2` never even runs.
  #
  # `f(n) = <audit_wrap>(f(n))` is `f = f` with one extra tuple layer
  # `certificate.ex` has no clause for. No argument to `f` is EVER threaded
  # through the self-call (there isn't one to thread -- `f`'s parameter `n`
  # is never even referenced), so under any evaluator this is an
  # unconditional infinite loop -- the same shape as the already-passing
  # `"a non-terminating global is rejected"` test in certificate_test.exs
  # (`loop : Dec = loop`), just with the self-reference nested one layer
  # deeper. It MUST be rejected.
  #
  # What actually happens: `calls?(:f, f_body)` recurses through the `:lam`
  # clause into the body, hits `{:audit_wrap, ...}`, has no clause for it,
  # falls to `calls?(_name, _term), do: false` -- so the WHOLE function is
  # reported as "doesn't call itself," and `terminating_ready?/3` returns
  # `true` outright without ever building a single change matrix.
  #
  # Idris's `Core/Termination/SizeChange.idr` (the file this module is
  # explicitly a port of) walks its own already-closed `CExp` grammar and
  # cannot have this shape of gap; Cure's Core term representation is open
  # tuples, so the walker needs to be fail-closed the way
  # `Validator.children/1` already is, and currently is not.
  test "T1: a self-call hidden inside an unrecognized wrapper node is falsely certified total" do
    ty = {:pi, {:type, 0}, {:type, 0}}
    # f(n) = <audit_wrap>(f(n)) -- literally f = f, wrapped; no argument ever
    # changes across the recursive call.
    body = {:lam, {:type, 0}, {:audit_wrap, {:app, {:global, :f}, {:var, 0}}}}
    env = Env.empty() |> Env.add_def(:f, ty, body)

    refute Certificate.terminating?(:f, body, env),
           "f(n) = f(n) (self-call wrapped in an unrecognized node) never decreases and " <>
             "must be rejected -- it must not be certified just because calls?/2 fails to " <>
             "see the self-call through the wrapper"
  end

  # T2: same root cause, reached through the cross-function/mutual size-change
  # path (`mutual_group_total?/5` + `function_edges/3`) instead of the
  # singleton fast path.
  #
  # certificate_test.exs already pins the UNWRAPPED version of this exact
  # scenario ("a mutually-recursive cycle f→g→f is NOT certified": f(x)=g(x),
  # g(x)=f(x), x never changes -- correctly rejected). Here f's call to g is
  # wrapped in the same unrecognized `:audit_wrap` node; g's call to f is
  # left untouched.
  #
  # `mutual_group/3` (SCC detection) uses the separate, tag-agnostic
  # `gather_globals` walk (a genuine `Tuple.to_list` traversal with no
  # per-shape case list) and so still correctly finds the 2-member group
  # {f, g} despite the wrapper. But `function_edges/3` -- which builds the
  # actual cross-function change matrices used for the accept/reject verdict
  # -- reuses the SAME fail-open `walk`, so f's wrapped call to g
  # contributes zero edges. The only edge that survives into the closure is
  # {g, f, [[:equal]]} (g's plain, visible call to f) -- a NON-endo edge
  # (g != f). `mutual_group_total?/5` only rejects on ENDO edges (pattern
  # `{f, f, m}`); every non-endo edge unconditionally passes
  # (`{_f, _g, _m} -> true`). A closure with zero endo edges therefore
  # satisfies `Enum.all?/2` vacuously, and the genuinely divergent,
  # non-decreasing cycle is certified total.
  test "T2: a mutual cycle with one leg hidden inside an unrecognized wrapper node is falsely certified total" do
    ty = {:pi, {:type, 0}, {:type, 0}}
    # f(x) = <audit_wrap>(g(x)) -- the call to g is hidden from the walker.
    f_body = {:lam, {:type, 0}, {:audit_wrap, {:app, {:global, :g}, {:var, 0}}}}
    # g(x) = f(x) -- ordinary, visible call back to f.
    g_body = {:lam, {:type, 0}, {:app, {:global, :f}, {:var, 0}}}
    env = Env.empty() |> Env.add_def(:f, ty, f_body) |> Env.add_def(:g, ty, g_body)

    refute Certificate.terminating?(:f, f_body, env),
           "f(x)=g(x), g(x)=f(x) with x never changing is the same divergent cycle " <>
             "certificate_test.exs already rejects when unwrapped -- hiding f's call to g " <>
             "inside an unrecognized node must not flip the verdict to certified, and must " <>
             "not do so by starving the endo-edge check of any edges to check at all"
  end
end
