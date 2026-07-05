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

  test "the connective primitives are retired: a residual connective prim is stuck" do
    # `and`/`or`/`not` are now Std.Bool case-defs, not primitives; a residual prim
    # no longer folds (it stays a stuck neutral).
    assert match?({:vneutral, _}, Eval.eval({:prim, :and, [{:ctor, :True, []}, {:ctor, :True, []}]}, []))
    assert match?({:vneutral, _}, Eval.eval({:prim, :not, [{:ctor, :False, []}]}, []))
  end

  test "Bool-operand equality is retired: only numeric :eq folds" do
    # `==` on Bool is now the Std.Bool def `eq`; the Bool-operand `:eq` prim is
    # gone, so a residual one is stuck. Numeric `:eq` still folds.
    assert match?({:vneutral, _}, Eval.eval({:prim, :eq, [{:ctor, :True, []}, {:ctor, :False, []}]}, []))
    assert Eval.eval({:prim, :eq, [{:int_lit, 3}, {:int_lit, 3}]}, []) == Eval.eval({:ctor, :True, []}, [])
  end
end
