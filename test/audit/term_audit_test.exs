defmodule Cure.Audit.TermTest do
  @moduledoc """
  Audit findings for `lib/cure/core/term.ex` (the Core term grammar +
  substitution/shift/lift machinery — de Bruijn TCB).

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test
  for the bug, why it is wrong, and what the reference implementations
  (Agda/Lean/Idris) do instead. Do not run this file automatically as part
  of the trusted-suite gate — it documents open findings, not yet-fixed
  regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.Term

  # ---------------------------------------------------------------------
  # S1-S4: `{:hole, name}` is a genuine, LIVE, currently-elaborator-produced
  # Core node — not a retired/dead form like `{:eq}`/`{:refl}`/`{:rewrite}`/
  # `{:sigma}`/`{:pair}`/`{:fst}`/`{:snd}`/`{:prim}`/`{:absurd}` (all of
  # which term.ex correctly and *deliberately* excludes — confirmed by
  # test/cure/core/eq_refl_retirement_test.exs, rewrite_retirement_test.exs,
  # and test/cure/core/absurd_leaf_test.exs, whose own moduledoc says
  # "Term.term? excludes it" as an intentional design decision for a
  # DELETED/dead-producer form).
  #
  # `{:hole, name}` is the opposite of dead: it is the kernel's supported
  # "typed gap" (design spec §6/M8.5, KERNEL.md "Holes are firewalled, not
  # trusted"). It is parsed generally by `parse_prefix` (parser.ex ~253-255,
  # so `?name` can appear in ANY expression position, not just a whole
  # function body), it type-checks via a dedicated kernel clause
  # (`Kernel.check(_ctx, {:hole, _name}, _expected), do: :ok`, kernel.ex:264),
  # `Env`/`Declarations` store it as a real definition body
  # (declarations.ex:146,475-476), `Certificate` special-cases hole-bodied
  # globals (certificate.ex:93,406), `Serialize` (the DIFFERENT, actually-used
  # s-expression serializer) encodes/decodes it (serialize.ex:27,148), and
  # `Validator`'s `no_hole` clause is `:warn` — not `:reject` — at dev time
  # (validator.ex:63), only flipping to `:reject` at the release boundary
  # (validator.ex:101). Two committed tests demonstrate it is a real,
  # currently-reachable NESTED shape, not merely a whole-body placeholder:
  #
  #   test/cure/elab/hole_test.exs:39-47 — the real elaborator produces
  #   `{:hole, "body"}` as a checked definition's body today.
  #
  #   test/cure/elab/emit_hole_firewall_test.exs:26-34 — a hole nested as the
  #   SCRUTINEE of a `:case`, itself nested inside an `:app`
  #   (`{:app, {:case, {:hole, "p"}, {:type, 0}, [id_branch]}, {:int_lit, 0}}`)
  #   is exactly the anticipated post-rewrite-retirement shape the K3
  #   pre-erase hole gate is built to catch.
  #
  # Despite this, term.ex's FIVE grammar-processing functions — `term?/1`,
  # `shift/3`, `subst/3`, `to_external/1`, `from_external/1` — have NO clause
  # for `{:hole, name}` and (except `term?`, which has a catch-all
  # `term?(_), do: false`) no catch-all either. This is inconsistent with the
  # SAME file's `closed?/1`/`has_free_var?/2`, whose own docstring explicitly
  # names `{:hole, _}` as a recognized "non-variable leaf" that is closed
  # (term.ex:122-124) — and which correctly handles it via the generic tuple
  # fallback (term.ex:144-145). So within this one module, `{:hole, name}`
  # is simultaneously "a leaf I know about" (closed?) and "not a term at
  # all" / "a crash" (term?, shift, subst, to_external, from_external).
  #
  # Agda's `Substitute`, Lean 4's `Expr` traversal, and Idris 2's `TT` all
  # treat their respective "hole"/metavariable leaf forms (`Agda.Meta`,
  # Lean's `Expr.mvar`, Idris's `TT`'s `Hole`) as ordinary leaves that
  # shift/substitute as identity — never as a form the substitution engine
  # doesn't know exists.

  # S1: `Term.term?/1` misclassifies a legitimate dev-time Core node as
  # ill-formed. Fix: add `def term?({:hole, name}), do: is_binary(name)`
  # (mirroring the shape everywhere else in the codebase constructs it —
  # declarations.ex:476, serialize.ex:27/148 — always a string).
  test "S1: term? recognises {:hole, name} as a well-formed Core node" do
    assert Term.term?({:hole, "body"})
  end

  # S2: `Term.shift/3` has no clause (and no catch-all) for `{:hole, name}`,
  # so shifting any term containing a hole crashes with FunctionClauseError
  # instead of treating the hole as an inert leaf — exactly how every other
  # variable-free leaf (`{:int_lit,_}`, `{:float_lit,_}`, `{:global,_}`, ...)
  # is already handled a few lines above in the same function.
  test "S2: shift treats {:hole, name} as an inert leaf (identity), like other leaves" do
    assert {:hole, "p"} == Term.shift({:hole, "p"}, 1, 0)
    assert {:hole, "p"} == Term.shift({:hole, "p"}, 3, 5)
  end

  # S2b: the crash is not confined to a bare top-level hole — it fires the
  # instant a hole sits under ANY of shift's structural-recursion clauses
  # (:app/:case/:ctor/:data/...), which is exactly the shape
  # emit_hole_firewall_test.exs pins as a legitimate pre-erase Core body
  # (a hole as a :case scrutinee nested inside an :app).
  test "S2b: shift descends through :app/:case into a nested hole without crashing" do
    id_branch = {:reflexive, 1, {:lam, {:type, 0}, {:var, 0}}}
    term = {:app, {:case, {:hole, "p"}, {:type, 0}, [id_branch]}, {:int_lit, 0}}

    assert {:app, {:case, {:hole, "p"}, {:type, 0}, [id_branch]}, {:int_lit, 0}} ==
             Term.shift(term, 1, 0)
  end

  # S3: `Term.subst/3` has the identical gap as S2 (no clause, no catch-all).
  # A hole carries no de Bruijn variables of its own, so substitution into it
  # must be the identity, exactly like `{:int_lit,_}`/`{:type,_}`/etc.
  test "S3: subst treats {:hole, name} as an inert leaf (identity), like other leaves" do
    assert {:hole, "p"} == Term.subst({:hole, "p"}, 0, {:int_lit, 5})
  end

  # S4: `Term.to_external/1` / `from_external/1` have no clause for
  # `{:hole, name}` and no catch-all, so they crash instead of round-tripping
  # it. This directly contradicts docs/KERNEL.md's "Serialization" claim
  # ("Core terms carry no PIDs, references, or closures, so every checked
  # term has a total, reversible JSON-able encoding") for any dev-time-valid
  # definition that still contains a hole — which, per K3, is an entirely
  # expected state for a definition mid-development (only the RELEASE/emit
  # boundary rejects it, not "checked"). The other, actually-used serializer
  # (`Cure.Core.Serialize`, serialize.ex:27/148) already does this correctly
  # for the identical node shape — `Term.to_external`/`from_external` is the
  # odd one out within the TCB's own term module.
  test "S4: to_external/from_external round-trips {:hole, name}" do
    hole = {:hole, "body"}
    assert hole == Term.from_external(Term.to_external(hole))
  end
end
