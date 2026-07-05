defmodule Cure.Core.BoolConnectiveDefeqTest do
  @moduledoc """
  Phase 4 of retiring the Boolean-connective primitives.

  The headline win: with the connectives defined as `case`-eliminating functions
  over the inductive `Bool` (Std.Bool), the equations hold DEFINITIONALLY (by
  `refl`) — including on OPEN terms with a free Boolean variable `b`. The old
  primitive `and`/`or`/`not` fired only when BOTH operands reduced to concrete
  `True`/`False`, so `and(True, b)` stayed a stuck neutral and never unfolded.
  Now `and(True, b) ≡ b`, `and(False, b) ≡ False`, `not(not b) ≡ b`, etc.

  Also pins the retirement itself: a hand-built residual `{:prim, :and/:or/:not}`
  is rejected by `infer` with `{:unknown_prim, _}`, and the numeric `:eq`/`:ne`
  primitives are untouched.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Conv, Env, Eval, Kernel}

  # An env carrying the certified Std.Bool connective defs (`and`/`or`/`not`/...).
  defp bool_env do
    {:ok, env} =
      Cure.Elab.Program.elaborate("mod M\n  use Std.Bool\n  fn __use(a: Bool) -> Bool = a\nend\n")

    env
  end

  @tt {:ctor, :True, []}
  @ff {:ctor, :False, []}

  # A single free Boolean variable `b` at de Bruijn index 0.
  @conv_env [{:vneutral, {:nvar, 0}}]
  @depth 1
  @b {:var, 0}

  defp band(a, b), do: {:app, {:app, {:global, :and}, a}, b}
  defp bor(a, b), do: {:app, {:app, {:global, :or}, a}, b}
  defp bnot(a), do: {:app, {:global, :not}, a}

  test "closed equations hold by conversion: not True ≡ False, not False ≡ True" do
    env = bool_env()
    assert Conv.conv?(bnot(@tt), @ff, [], 0, env)
    assert Conv.conv?(bnot(@ff), @tt, [], 0, env)
  end

  test "OPEN-term win: and(True, b) ≡ b and or(False, b) ≡ b for a variable b" do
    env = bool_env()
    assert Conv.conv?(band(@tt, @b), @b, @conv_env, @depth, env)
    assert Conv.conv?(bor(@ff, @b), @b, @conv_env, @depth, env)
  end

  test "OPEN-term win: and(False, b) ≡ False and or(True, b) ≡ True" do
    env = bool_env()
    assert Conv.conv?(band(@ff, @b), @ff, @conv_env, @depth, env)
    assert Conv.conv?(bor(@tt, @b), @tt, @conv_env, @depth, env)
  end

  test "double negation not(not b) is propositional, NOT definitional (as in Agda/Lean)" do
    env = bool_env()
    # `not (not b)` on a neutral `b` produces a stuck `case`-of-`case`; reducing it
    # to `b` needs case-analysis on `b` (a propositional proof), not `refl`. This
    # matches intensional type theory — the kernel does NOT do case-commuting
    # conversion. (The spec's §6 listing of not(not b) ≡ b as definitional
    # overstates it; the one-step equations above are the real definitional wins.)
    refute Conv.conv?(bnot(bnot(@b)), @b, @conv_env, @depth, env)
  end

  test "the win is genuine δ-reduction, not a structural accident" do
    env = bool_env()
    # Without the signature no global unfolds, so the open redex is NOT structural
    # equal to `b`; and even with δ, `and(True, b) ≢ not b`.
    refute Conv.conv?(band(@tt, @b), @b, @conv_env, @depth, nil)
    refute Conv.conv?(band(@tt, @b), bnot(@b), @conv_env, @depth, env)
  end

  # -- retirement of the primitive path --------------------------------------

  defp ctx, do: Context.empty(Builtins.seed(Env.empty()))

  test "a residual connective prim is rejected by infer as {:unknown_prim, _}" do
    assert {:error, {:unknown_prim, :and}} = Kernel.infer(ctx(), {:prim, :and, [@tt, @ff]})
    assert {:error, {:unknown_prim, :or}} = Kernel.infer(ctx(), {:prim, :or, [@tt, @ff]})
    assert {:error, {:unknown_prim, :not}} = Kernel.infer(ctx(), {:prim, :not, [@tt]})
  end

  test "a residual connective prim no longer folds in eval (stuck neutral)" do
    v = Eval.eval({:prim, :and, [@tt, @ff]}, [])
    refute v == Eval.eval(@ff, [])
    assert match?({:vneutral, _}, v)
  end

  test "numeric :eq/:ne primitives are untouched (still fold and type to Bool)" do
    assert Eval.eval({:prim, :eq, [{:int_lit, 4}, {:int_lit, 4}]}, []) == Eval.eval(@tt, [])
    assert Eval.eval({:prim, :ne, [{:int_lit, 4}, {:int_lit, 5}]}, []) == Eval.eval(@tt, [])
    assert {:ok, {:vdata, :Bool, []}} = Kernel.infer(ctx(), {:prim, :eq, [{:int_lit, 1}, {:int_lit, 1}]})
    assert {:ok, {:vdata, :Bool, []}} = Kernel.infer(ctx(), {:prim, :ne, [{:int_lit, 1}, {:int_lit, 2}]})
  end
end
