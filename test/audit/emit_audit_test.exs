defmodule Cure.Audit.EmitTest do
  @moduledoc """
  Audit findings for `lib/cure/elab/emit.ex` (BEAM emission for the erased
  Core — design spec §8, M9.3).

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test
  for the bug and why it is wrong. Do not run this file automatically as
  part of the trusted-suite gate — it documents open findings, not
  yet-fixed regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{Emit, Program}

  # ---------------------------------------------------------------------
  # EM1: `extern_form/2` (emit.ex ~136) builds the emitted function's BEAM
  # arity — and the number of Erlang params it feeds to the remote call —
  # directly from the raw integer literal the user writes in
  # `@extern(:mod, :fun, ARITY)`. It never consults the def's OWN
  # `:present`-quantity list the way every OTHER arity computation in this
  # file does (`real_function_form`'s `params = for {n, :present} <- ...`,
  # and `present_arity/2`, which every CALL SITE uses to decide how many
  # arguments to pass). Nothing in `declarations.ex`'s extern branch
  # (`elaborate_function_body`, ~161-172) cross-checks the literal against
  # `sig.quantities`'s present-count either — the two numbers are free to
  # diverge.
  #
  # An extern signature with an erased/implicit parameter (`{T: Type}`,
  # exactly like any other Cure function — auto-generalization inserts one
  # for a free lowercase type var even if the user never writes it
  # explicitly) has a present-arity strictly smaller than its surface
  # Pi-telescope length. A user who counts the parens when filling in
  # `ARITY` (2, for `head({T: Type}, xs: List(T))`) — the natural reading,
  # since the erased/present split is an internal compiler concept —
  # produces a module where `extern_form` emits `head/2` while every Cure
  # call site (via `present_arity/2`, reading the SAME `sig.quantities`)
  # invokes `head/1`. The module still compiles as isolated forms, but the
  # two numbers were never forced to agree, so ordinary calling code breaks.
  #
  # Correct behavior: `extern_form` should derive its arity from the def's
  # own present-quantity count (mirroring `real_function_form`), so the
  # `@extern` arity is exactly the number of REAL (present) BEAM arguments
  # the target function receives — internally self-consistent regardless
  # of what a user habitually counts.
  test "EM1: an extern signature with an erased implicit param compiles and calls correctly" do
    src = """
    mod M
      @extern(:erlang, :hd, 2)
      fn head({T: Type}, xs: List(T)) -> T
      fn use_head(xs: List(Int)) -> Int = head(xs)
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env,
               module: :"Cure.Audit.ExternErasedArity",
               functions: [:head, :use_head]
             )

    assert apply(mod, :use_head, [[1, 2, 3]]) == 1
  end

  # ---------------------------------------------------------------------
  # EM2: `float_div` and `int_div` are DISTINCT builtin-op globals
  # (`Cure.Core.Builtins.@int_binops`/`@float_binops`), registered with the
  # SAME op_key `:div` (builtins.ex:40,60) — a deliberate design choice so
  # the certified-δ normalizer's `builtin_op_fold` can share one clause per
  # op_key. But `emit.ex`'s `builtin_op_form/4` (~294-299) discards the
  # GLOBAL NAME (`g`, e.g. `:float_div`) and hands ONLY the collapsed
  # `op_key` (`:div`) to `lower_builtin_op/4` — the int/float distinction
  # present at every other layer (kernel, normalizer, elaborator's
  # `@int_binop_globals` vs `@float_binop_globals`) is lost at exactly this
  # point. `erl_binop(:div)` (emit.ex ~433) then unconditionally emits
  # Erlang's `div` operator — which is INTEGER-ONLY (`erlang:'div'/2`
  # raises `ArithmeticError`/badarith on float operands; it is not the
  # general division operator, that is `/`). So `Std.Float`'s `/` — reached
  # via a non-constant-folded (variable, not literal) division — lowers to
  # a call that crashes at runtime instead of computing a float quotient.
  #
  # `test/cure/core/float_prim_test.exs` only exercises the KERNEL's
  # compile-time normalizer (`Normalise.nf` with `delta: :certified`, which
  # folds literal `float_div` spines using Elixir's native `/` in
  # `normalise.ex`'s OWN, separate `builtin_op_fold` clause) — it never
  # reaches `emit.ex`'s runtime lowering, so it does not cover this. No
  # existing test exercises `/` on non-literal (variable) `Float` operands
  # end-to-end through `Emit`.
  #
  # Correct behavior: `favg(a, b) = a / b` on two `Float` arguments must
  # compute a real float quotient, not crash.
  test "EM2: Float division on variable (non-folded) operands computes a float quotient, not a crash" do
    src = """
    mod M
      use Std.Bool
      fn favg(a: Float, b: Float) -> Float = a / b
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Audit.FloatDiv", functions: [:favg])

    assert apply(mod, :favg, [7.0, 2.0]) == 3.5
  end
end
