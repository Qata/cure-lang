defmodule Cure.Core.PrimBoolEvalTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Eval

  test "eval folds a comparison to the True constructor value" do
    v = Eval.eval({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, [])
    assert v == Eval.eval({:ctor, :True, []}, [])
    refute v == {:vbool, true}
  end

  test "eval folds a false comparison to the False constructor value" do
    v = Eval.eval({:prim, :lt, [{:int_lit, 5}, {:int_lit, 3}]}, [])
    assert v == Eval.eval({:ctor, :False, []}, [])
  end

  test "eval folds a connective over constructor-value operands" do
    tt = Eval.eval({:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]}, [])
    ff = Eval.eval({:prim, :lt, [{:int_lit, 2}, {:int_lit, 1}]}, [])
    assert Eval.eval({:prim, :and, [{:ctor, :True, []}, {:ctor, :True, []}]}, []) == tt
    assert Eval.eval({:prim, :and, [{:ctor, :True, []}, {:ctor, :False, []}]}, []) == ff
    assert Eval.eval({:prim, :not, [{:ctor, :False, []}]}, []) == tt
  end

  test "eval folds Bool-operand equality" do
    tt = Eval.eval({:ctor, :True, []}, [])
    assert Eval.eval({:prim, :eq, [{:ctor, :True, []}, {:ctor, :True, []}]}, []) == tt
    assert Eval.eval({:prim, :eq, [{:ctor, :True, []}, {:ctor, :False, []}]}, []) ==
             Eval.eval({:ctor, :False, []}, [])
  end
end
