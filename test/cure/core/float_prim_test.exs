defmodule Cure.Core.FloatPrimTest do
  @moduledoc """
  Primitive `Float` in the kernel — the remaining numeric gap so float-indexed
  types (`Rate`, `PositiveAmount`, …) evaluate and compare inside `Cure.Core`
  rather than in the faked layer.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Eval, Kernel, Quote}

  test "eval folds float arithmetic" do
    assert Eval.eval({:prim, :add, [{:float_lit, 1.5}, {:float_lit, 2.0}]}, []) == {:vfloat, 3.5}
    assert Eval.eval({:prim, :mul, [{:float_lit, 2.0}, {:float_lit, 3.0}]}, []) == {:vfloat, 6.0}
    assert Eval.eval({:prim, :div, [{:float_lit, 7.0}, {:float_lit, 2.0}]}, []) == {:vfloat, 3.5}
  end

  test "eval folds float comparisons to Bool constructor values" do
    assert Eval.eval({:prim, :lt, [{:float_lit, 1.0}, {:float_lit, 2.0}]}, []) ==
             Eval.eval({:ctor, :True, []}, [])
  end

  test "reify round-trips Float type and literals" do
    assert Quote.reify({:vfloat_type}) == {:float_type}
    assert Quote.reify({:vfloat, 3.5}) == {:float_lit, 3.5}
  end

  test "definitional equality on floats" do
    assert Conv.conv?({:prim, :add, [{:float_lit, 1.5}, {:float_lit, 2.0}]}, {:float_lit, 3.5}, [], 0)
    refute Conv.conv?({:float_lit, 3.5}, {:float_lit, 3.6}, [], 0)
  end

  test "kernel types Float literals and arithmetic" do
    ctx = Context.empty(Builtins.seed(Env.empty()))
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx, {:float_type})
    assert {:ok, {:vfloat_type}} = Kernel.infer(ctx, {:float_lit, 1.5})
    assert {:ok, {:vfloat_type}} = Kernel.infer(ctx, {:prim, :add, [{:float_lit, 1.0}, {:float_lit, 2.0}]})

    assert {:ok, {:vdata, :Bool, []}} =
             Kernel.infer(ctx, {:prim, :lt, [{:float_lit, 1.0}, {:float_lit, 2.0}]})

    assert {:error, _} = Kernel.infer(ctx, {:prim, :add, [{:float_lit, 1.0}, {:int_lit, 2}]})
  end
end
