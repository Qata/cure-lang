defmodule Cure.Core.BoolPrimTest do
  @moduledoc """
  Comparisons and boolean connectives in the kernel. `Bool` is now a real
  inductive family (retiring the primitive `{:bool_type}`/`{:bool_lit}`/`bool_elim`
  forms): comparisons/connectives infer to the `Bool` inductive type value and
  `eval` folds them to the `True`/`False` constructor values.
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

  test "eval folds boolean connectives over constructor-value operands" do
    assert Eval.eval({:prim, :and, [{:ctor, :True, []}, {:ctor, :False, []}]}, []) == vfalse()
    assert Eval.eval({:prim, :or, [{:ctor, :True, []}, {:ctor, :False, []}]}, []) == vtrue()
    assert Eval.eval({:prim, :not, [{:ctor, :False, []}]}, []) == vtrue()
  end

  test "definitional equality across comparisons" do
    assert Conv.conv?({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, {:ctor, :True, []}, [], 0)
    refute Conv.conv?({:ctor, :True, []}, {:ctor, :False, []}, [], 0)
  end

  test "kernel types comparisons and connectives at the Bool inductive" do
    bool = {:vdata, :Bool, []}
    assert {:ok, ^bool} = Kernel.infer(ctx(), {:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]})

    assert {:ok, ^bool} =
             Kernel.infer(ctx(), {:prim, :and, [{:ctor, :True, []}, {:ctor, :False, []}]})

    assert {:error, _} = Kernel.infer(ctx(), {:prim, :and, [{:int_lit, 1}, {:int_lit, 2}]})
    assert {:error, _} = Kernel.infer(ctx(), {:prim, :lt, [{:ctor, :True, []}, {:int_lit, 2}]})
  end
end
