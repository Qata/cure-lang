defmodule Antigen.Assays.PositivityTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Positivity, as: A
  alias Antigen.Generators.Positivity, as: G

  test "passes a labeled-negative family (checker correctly rejects it)" do
    assert :ok == A.run(G.negative_family())
  end

  test "passes a labeled-positive family (checker accepts it)" do
    assert :ok == A.run(G.positive_family())
  end

  test "a mislabeled family (labeled positive but actually negative) is a violation" do
    mislabeled = %{G.negative_family() | label: :positive}
    assert {:violation, _} = A.run(mislabeled)
  end
end
