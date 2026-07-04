defmodule Cure.Core.BoolPrimTest do
  @moduledoc """
  Numeric comparisons in the kernel. `Bool` is a real inductive family (retiring
  the primitive `{:bool_type}`/`{:bool_lit}`/`bool_elim` forms): comparisons infer
  to the `Bool` inductive type value and `eval` folds them to the `True`/`False`
  constructor values. The boolean CONNECTIVES (`and`/`or`/`not`) and Bool-operand
  equality are no longer primitives — they are Std.Bool `case`-defs — so a residual
  connective prim is stuck in `eval` and `{:unknown_prim, _}` in `infer`.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Eval, Kernel}

  defp ctx, do: Context.empty(Builtins.seed(Env.empty()))
  defp vtrue, do: Eval.eval({:ctor, :True, []}, [])
  defp vfalse, do: Eval.eval({:ctor, :False, []}, [])

  test "eval folds integer comparisons to Bool constructor values" do
    assert Eval.eval({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, []) == vtrue()
    assert Eval.eval({:prim, :eq, [{:int_lit, 4}, {:int_lit, 4}]}, []) == vtrue()
    assert Eval.eval({:prim, :ge, [{:int_lit, 2}, {:int_lit, 9}]}, []) == vfalse()
  end

  test "the boolean-connective primitives are retired: a residual prim is stuck" do
    # `and`/`or`/`not` are no longer kernel primitives (they are Std.Bool case-defs
    # booland/boolor/boolnot). A hand-built residual prim no longer folds.
    assert match?({:vneutral, _}, Eval.eval({:prim, :and, [{:ctor, :True, []}, {:ctor, :False, []}]}, []))
    assert match?({:vneutral, _}, Eval.eval({:prim, :or, [{:ctor, :True, []}, {:ctor, :False, []}]}, []))
    assert match?({:vneutral, _}, Eval.eval({:prim, :not, [{:ctor, :False, []}]}, []))
  end

  test "definitional equality across comparisons" do
    assert Conv.conv?({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, {:ctor, :True, []}, [], 0)
    refute Conv.conv?({:ctor, :True, []}, {:ctor, :False, []}, [], 0)
  end

  test "kernel types numeric comparisons at Bool and rejects retired connective prims" do
    bool = {:vdata, :Bool, []}
    assert {:ok, ^bool} = Kernel.infer(ctx(), {:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]})

    # The connectives are retired as primitives — a residual `:and` prim is rejected.
    assert {:error, {:unknown_prim, :and}} =
             Kernel.infer(ctx(), {:prim, :and, [{:ctor, :True, []}, {:ctor, :False, []}]})

    assert {:error, _} = Kernel.infer(ctx(), {:prim, :lt, [{:ctor, :True, []}, {:int_lit, 2}]})
  end
end
