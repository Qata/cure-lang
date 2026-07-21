defmodule Cure.Elab.RewriteCommandTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Grade
  alias Cure.Elab.Rewrite

  test "occurrence traversal is left-to-right and binder-aware" do
    target = {:var, 0}

    goal =
      {:pi, Grade.unrestricted(), {:int_type},
       {:data, :"Std.Equivalent#Equivalent", [{:int_type}], [{:var, 1}, {:var, 1}]}}

    occurrences = Rewrite.occurrences(goal, target)
    assert Enum.map(occurrences, & &1.number) == [1, 2]
    assert Enum.map(occurrences, & &1.traversal_path) == [[2, 2, 0], [2, 2, 1]]
    assert Enum.all?(occurrences, &match?([:normalized_goal | _], &1.source_path))
  end

  test "nested application occurrences retain stable traversal paths" do
    target = {:var, 0}
    goal = {:app, {:global, :outer}, {:app, {:global, :inner}, target}}

    assert [%Rewrite.Occurrence{number: 1, traversal_path: [1, 1]}] = Rewrite.occurrences(goal, target)
  end
end
