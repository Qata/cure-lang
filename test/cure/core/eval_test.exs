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

  test "iota: a case on a constructor selects that constructor's branch" do
    motive = {:lam, {:data, :Dec, [], []}, {:type, 2}}
    branches = [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 1}}]
    cas = {:case, {:ctor, :Causal, []}, motive, branches}
    assert {:vtype, 1} == Eval.eval(cas, [])
  end

  test "iota: a case binds the constructor's arguments in the branch body" do
    # case (mk Type0) of { mk x -> x } ⇝ Type0
    motive = {:lam, {:data, :Box, [], []}, {:type, 1}}
    branches = [{:mk, 1, {:var, 0}}]
    cas = {:case, {:ctor, :mk, [{:type, 0}]}, motive, branches}
    assert {:vtype, 0} == Eval.eval(cas, [])
  end

  test "iota: a case on a neutral scrutinee stays a neutral case" do
    motive = {:lam, {:data, :Dec, [], []}, {:type, 0}}
    branches = [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]
    cas = {:case, {:var, 0}, motive, branches}
    assert {:vneutral, {:ncase, {:nvar, 0}, _m, _b}} = Eval.eval(cas, [{:vneutral, {:nvar, 0}}])
  end
end
