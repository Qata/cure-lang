defmodule Cure.Audit.CoreSmallTest do
  @moduledoc """
  Audit findings for four small trusted-Core modules: `Cure.Core.Universe`,
  `Cure.Core.Context`, `Cure.Core.MetaCheck`, `Cure.Core.Value`
  (lib/cure/core/{universe,context,meta_check,value}.ex).

  Each test below is a specific, currently-RED executable claim about behavior
  the audit believes is correct. See the comment above each test for the bug,
  why it is wrong, and what a reference kernel (Agda/Lean/Idris) does instead.
  Do not run this file automatically as part of the trusted-suite gate — it
  documents open findings, not yet-fixed regressions.

  `Cure.Core.Universe` has NO findings here: `Universe.succ(Universe.ceiling())`
  erroring (so `Type <ceiling>` can never itself be used as an explicit
  classifier/domain) is fully covered by the existing `universe_test.exs` and is
  independently confirmed as INTENTIONAL by
  docs/superpowers/specs/2026-07-02-antigen-mutation-corpus-design.md:180-182,
  which deliberately caps mutation-testing goals below the ceiling for exactly
  this reason. Not a bug — see the final audit report for the full reasoning.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.{Context, Eval, Kernel, MetaCheck, Term, Value}

  # ---------------------------------------------------------------------
  # X1/X2: a NEGATIVE de Bruijn index silently resolves to the WRONG binding
  # instead of failing, at both the Context layer (X1) and the kernel's actual
  # trust boundary (X2). Root cause: `Context.lookup/2` is
  #
  #     def lookup(%__MODULE__{types: ts}, k), do: Enum.at(ts, k)
  #
  # and Elixir's `Enum.at/2` treats a NEGATIVE index as counting from the END
  # of the list (`Enum.at([:a, :b], -1) == :b`), not as "out of range". A de
  # Bruijn index is by definition non-negative — `Term.term?({:var, k})`
  # itself requires `is_integer(k) and k >= 0` — so a negative index denotes a
  # malformed/out-of-range variable reference. Every reference implementation
  # (and every other invalid-index path in this same function — an index too
  # LARGE already correctly returns `nil`) treats an invalid variable
  # reference as a hard failure, never a silent alias to some other binding.
  # ---------------------------------------------------------------------

  describe "Context.lookup/2 (X)" do
    test "X1: a negative index must fail lookup like an out-of-range one, not wrap to the last binding" do
      ctx =
        Context.empty()
        |> Context.extend({:vint_type})
        |> Context.extend({:vtype, 0})

      # Sanity: normal in-range lookups behave exactly as documented.
      assert Context.lookup(ctx, 0) == {:vtype, 0}
      assert Context.lookup(ctx, 1) == {:vint_type}
      # An index too LARGE is already, correctly, out of range:
      assert Context.lookup(ctx, 2) == nil

      # A negative index is EQUALLY out of range and must fail the same way —
      # today it instead silently returns `ctx.types`'s LAST element via
      # Elixir's negative-`Enum.at/2` "count from the end" semantics.
      assert Context.lookup(ctx, -1) == nil
    end
  end

  describe "Kernel.infer/2 via Context.lookup/2 (X)" do
    # X2 is X1's consequence at the actual trust boundary. `Kernel.infer/2`'s
    # `{:var, k}` clause has NO guard on `k` and nothing in `check_def/2`,
    # `infer/2`, or `check/3` calls `Term.term?/1` before checking (confirmed
    # by grep — `Term.term?/1` is called nowhere in the live check/infer/eval
    # path, only from tests and Antigen's own fuzz-corpus validators). So a
    # `{:var, -1}` occurring anywhere a variable is expected — e.g. inside a
    # deserialized proof-carrying artifact reconstructed by the untrusted
    # `Term.from_external/1` (KERNEL.md's own "independent checker" use case,
    # which likewise never validates `Term.term?/1` before re-checking) — is
    # silently accepted and TYPED AS THE WRONG VARIABLE, rather than rejected
    # as `{:error, {:unbound_var, -1}}` like every other invalid reference.
    test "X2: a structurally-invalid negative variable index type-checks as the wrong binding instead of failing" do
      ctx =
        Context.empty()
        |> Context.extend({:vint_type})
        |> Context.extend({:vtype, 0})

      # {:var, -1} is not a well-formed Core term by the kernel's own grammar
      # contract...
      refute Term.term?({:var, -1})

      # ...yet the trusted kernel accepts it and reports it as well-typed,
      # silently borrowing the OLDEST binding's type ({:vint_type}) instead of
      # failing the way every other unbound/out-of-range variable does.
      assert Kernel.infer(ctx, {:var, -1}) == {:error, {:unbound_var, -1}}
    end
  end

  # ---------------------------------------------------------------------
  # W1: the same unguarded-negative-index gap (X1/X2) lets the trusted
  # EVALUATOR construct a semantic value that violates `Value.value?/1`'s own
  # documented well-formedness invariant.
  #
  #     def eval({:var, k}, env) do
  #       case Enum.at(env, k) do
  #         nil -> {:vneutral, {:nvar, k}}
  #         v -> v
  #       end
  #     end
  #
  # For a negative `k` against an EMPTY env there is no wraparound target, so
  # `Enum.at([], k)` is `nil` and `Eval.eval` falls through to
  # `{:vneutral, {:nvar, k}}` VERBATIM — with the negative `k` still attached.
  # But `Value.neutral?({:nvar, level})` (and therefore `Value.value?/1`)
  # explicitly requires `is_integer(level) and level >= 0` — value.ex's own
  # moduledoc calls a neutral's head a de Bruijn *level*, and a level, like an
  # index, is never negative. So the trusted evaluator can hand back a value
  # that the Core's own value-well-formedness predicate rejects as malformed.
  # ---------------------------------------------------------------------

  describe "Eval.eval/2 vs Value.value?/1 (W)" do
    test "W1: evaluating an out-of-range var builds a neutral that Value.value?/1 itself rejects" do
      bad = Eval.eval({:var, -1}, [])
      assert bad == {:vneutral, {:nvar, -1}}

      # Whatever `Eval.eval/2` returns is documented (`@spec eval(Term.t(),
      # [Value.t()]) :: Value.t()`) to be a well-formed semantic value — it
      # must satisfy the Core's own value predicate, not construct a neutral
      # with a negative de Bruijn level.
      assert Value.value?(bad)
    end
  end

  # ---------------------------------------------------------------------
  # M1: `MetaCheck.progresses?/2` (and `type_preserved?/2`, same root cause)
  # CRASHES instead of returning `false` when handed a term containing
  # `{:hole, name}` — a real, currently-producible Core node, not a
  # retired/dead one (confirmed independently by test/audit/term_audit_test.exs
  # S1-S4: `{:hole, name}` is parsed generally, type-checks via a dedicated
  # kernel clause `Kernel.check(_ctx, {:hole, _name}, _expected), do: :ok`,
  # is stored as a real definition body, and is special-cased by
  # Certificate/Serialize/Validator — Validator's `no_hole` clause is only
  # `:warn` at dev time, `:reject` at release, i.e. a hole is legitimately
  # present in a checked-but-unfinished Core term today).
  #
  # But `Kernel.infer/2` — which BOTH `type_preserved?/2` and `progresses?/2`
  # call FIRST — has NO clause for `{:hole, _}` at all (a hole only ever
  # type-checks in CHECKING mode, against an expected type). Asking the kernel
  # to INFER one raises `FunctionClauseError`, an ordinary Elixir exception
  # that escapes MetaCheck's `with`/`case` (which only pattern-matches
  # `{:ok, _}`/`{:error, _}` result TUPLES, never exceptions) and crashes the
  # caller instead of yielding the documented `false` for "not type
  # preserved" / "does not progress". A metatheory guardrail that crashes on
  # real, live input — rather than reporting a clean verdict — cannot be
  # batch-run over any corpus that includes an in-progress (holed) definition
  # without an unrelated crash halting the whole run.
  # ---------------------------------------------------------------------

  describe "MetaCheck.progresses?/2 on a live hole node (M)" do
    test "M1: progresses?/2 must report false on a hole instead of crashing" do
      ctx = Context.empty()
      assert MetaCheck.progresses?(ctx, {:hole, "x"}) == false
    end
  end
end
