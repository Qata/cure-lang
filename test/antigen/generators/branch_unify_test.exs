defmodule Antigen.Generators.BranchUnifyTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.BranchUnify
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays}

  @sample 300

  test "every sampled branch-unify probe's verdict agrees with the live kernel" do
    for %Challenge{} = c <- B.interp(BranchUnify.gen()) |> Enum.take(@sample) do
      assert c.kind == :branch_unify
      assert c.label in [:trivial, :solved, :impossible]
      assert Assays.BranchUnify.run(c) == :ok,
             "verdict oracle disagreed on #{c.note} (#{c.label})"
    end
  end

  test "the case menu spans all three verdicts and the key unifier arms" do
    labels = BranchUnify.cases() |> Enum.map(fn {_n, _d, _c, _i, v, _note} -> v end) |> MapSet.new()
    assert MapSet.equal?(labels, MapSet.new([:trivial, :solved, :impossible]))

    notes = BranchUnify.cases() |> Enum.map(fn t -> elem(t, 5) end)
    for frag <- ["merge conflict", "forced equation", "rigid data/Type", "outer index var"] do
      assert Enum.any?(notes, &String.contains?(&1, frag)), "missing arm: #{frag}"
    end
  end
end
