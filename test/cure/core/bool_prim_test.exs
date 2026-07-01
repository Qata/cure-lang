defmodule Cure.Core.BoolPrimTest do
  @moduledoc """
  Primitive `Bool`, comparisons, and boolean connectives in the kernel — the rest
  of the arithmetic/logic surface the `Cure.Types.Reduce` fold covered, now owned
  by `Cure.Core` so refinement predicates evaluate inside the kernel.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Conv, Eval, Kernel, Quote}

  test "eval folds integer comparisons to booleans" do
    assert Eval.eval({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, []) == {:vbool, true}
    assert Eval.eval({:prim, :eq, [{:int_lit, 4}, {:int_lit, 4}]}, []) == {:vbool, true}
    assert Eval.eval({:prim, :ge, [{:int_lit, 2}, {:int_lit, 9}]}, []) == {:vbool, false}
  end

  test "eval folds boolean connectives" do
    assert Eval.eval({:prim, :and, [{:bool_lit, true}, {:bool_lit, false}]}, []) == {:vbool, false}
    assert Eval.eval({:prim, :or, [{:bool_lit, true}, {:bool_lit, false}]}, []) == {:vbool, true}
    assert Eval.eval({:prim, :not, [{:bool_lit, false}]}, []) == {:vbool, true}
  end

  test "reify round-trips Bool type and literals" do
    assert Quote.reify({:vbool_type}) == {:bool_type}
    assert Quote.reify({:vbool, true}) == {:bool_lit, true}
  end

  test "definitional equality across comparisons" do
    assert Conv.conv?({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, {:bool_lit, true}, [], 0)
    refute Conv.conv?({:bool_lit, true}, {:bool_lit, false}, [], 0)
  end

  test "kernel types Bool, comparisons, and connectives" do
    ctx = Context.empty()
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx, {:bool_type})
    assert {:ok, {:vbool_type}} = Kernel.infer(ctx, {:bool_lit, true})
    assert {:ok, {:vbool_type}} = Kernel.infer(ctx, {:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]})

    assert {:ok, {:vbool_type}} =
             Kernel.infer(ctx, {:prim, :and, [{:bool_lit, true}, {:bool_lit, false}]})

    assert {:error, _} = Kernel.infer(ctx, {:prim, :and, [{:int_lit, 1}, {:int_lit, 2}]})
    assert {:error, _} = Kernel.infer(ctx, {:prim, :lt, [{:bool_lit, true}, {:int_lit, 2}]})
  end
end
