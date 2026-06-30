defmodule Cure.Core.ValueTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Value

  test "recognises each value shape" do
    cl = {:closure, [], {:var, 0}}
    assert Value.value?({:vtype, 0})
    assert Value.value?({:vpi, {:vtype, 0}, cl})
    assert Value.value?({:vlam, {:vtype, 0}, cl})
    assert Value.value?({:vsigma, {:vtype, 0}, cl})
    assert Value.value?({:vpair, {:vtype, 0}, {:vtype, 1}})
    assert Value.value?({:vneutral, {:nvar, 0}})
    assert Value.value?({:vdata, :SF, [{:vtype, 0}]})
    assert Value.value?({:vctor, :seq, [{:vtype, 0}]})
    refute Value.value?({:vtype, 3})
    refute Value.value?(:nope)
  end

  test "recognises each neutral shape" do
    assert Value.neutral?({:nvar, 0})
    assert Value.neutral?({:nglobal, :and})
    assert Value.neutral?({:napp, {:nvar, 0}, {:vtype, 0}})
    assert Value.neutral?({:nfst, {:nvar, 0}})
    assert Value.neutral?({:nsnd, {:nvar, 0}})

    assert Value.neutral?(
             {:ncase, {:nvar, 0}, {:closure, [], {:type, 0}},
              [{:prim, 0, {:closure, [], {:type, 0}}}]}
           )

    refute Value.neutral?({:nvar, -1})
    refute Value.neutral?(:nope)
  end

  test "a closure carries an env (list of values) and a term" do
    assert Value.closure?({:closure, [], {:var, 0}})
    assert Value.closure?({:closure, [{:vtype, 0}], {:var, 0}})
    refute Value.closure?({:closure, :not_a_list, {:var, 0}})
    refute Value.closure?({:closure, [], :not_a_term})
  end
end
