defmodule Antigen.BuiltinBoolDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Eval}

  # Task 6 hardcodes :True/:False in eval.ex's fold (it has no sig on its path);
  # Task 2/3 seed the schema. This antibody fails if the two ever drift.
  test "fold's hardcoded True/False agree with the seeded :bool schema names" do
    names = Builtins.schema(:bool) |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    assert names == [:False, :True]

    assert Eval.eval({:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]}, []) ==
             Eval.eval({:ctor, :True, []}, [])

    assert Eval.eval({:prim, :lt, [{:int_lit, 2}, {:int_lit, 1}]}, []) ==
             Eval.eval({:ctor, :False, []}, [])
  end
end
