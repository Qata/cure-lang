defmodule Cure.Core.EvalTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Eval

  test "beta-reduces an application" do
    assert {:vtype, 0} == Eval.eval({:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}}, [])
  end

  test "iota-reduces pair projections on a value pair" do
    pair = {:pair, {:type, 0}, {:type, 1}}
    assert {:vtype, 0} == Eval.eval({:fst, pair}, [])
    assert {:vtype, 1} == Eval.eval({:snd, pair}, [])
  end

  test "a free variable evaluates to a neutral var" do
    assert {:vneutral, {:nvar, _}} = Eval.eval({:var, 0}, [])
  end

  test "an uncertified global evaluates to a neutral global (opaque until delta)" do
    assert {:vneutral, {:nglobal, :and}} == Eval.eval({:global, :and}, [])
  end

  test "a stuck projection on a neutral stays neutral" do
    assert {:vneutral, {:nfst, {:nvar, 0}}} ==
             Eval.eval({:fst, {:var, 0}}, [{:vneutral, {:nvar, 0}}])
  end

  test "apply extends the environment with the argument at index 0" do
    vlam = Eval.eval({:lam, {:type, 0}, {:var, 0}}, [])
    assert {:vtype, 1} == Eval.apply(vlam, {:vtype, 1})
  end
end
