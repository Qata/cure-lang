defmodule Antigen.Generators.PositivityTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Positivity
  alias Antigen.Corpus
  alias Cure.Core.Inductive

  defp verdict(c) do
    env = Positivity.env_of(c)
    Inductive.positive?(env, Inductive.get_family(env, c.payload.family.name))
  end

  test "negative_family is labeled :negative and the checker rejects it" do
    c = Positivity.negative_family()
    assert c.label == :negative
    assert {:error, {:non_strictly_positive, _}} = verdict(c)
  end

  test "positive_family is labeled :positive and the checker accepts it" do
    c = Positivity.positive_family()
    assert c.label == :positive
    assert :ok == verdict(c)
  end

  test "both families round-trip through the corpus with the checker verdict preserved" do
    for c <- [Positivity.positive_family(), Positivity.negative_family()] do
      line = Corpus.encode_record(c)
      assert {:ok, c2} = Corpus.decode_record(line)
      assert verdict(c2) == verdict(c)
    end
  end

  test "the richer single-family negatives are correctly labeled and rejected" do
    for c <- [Positivity.double_negation_family(), Positivity.sigma_negative_family()] do
      assert c.label == :negative
      assert {:error, {:non_strictly_positive, _}} = verdict(c),
             "checker should reject #{c.note}"
    end
  end

  test "gen/1 draws the richer negative shapes (deep positivity coverage), all label-correct" do
    sample = Antigen.Backend.StreamData.interp(Positivity.gen()) |> Enum.take(400)

    notes = sample |> Enum.map(& &1.note) |> MapSet.new()
    assert Enum.any?(notes, &(&1 =~ "double negation")), "double-negation shape never drawn"
    assert Enum.any?(notes, &(&1 =~ "sigma")), "sigma-negative shape never drawn"

    # every drawn family's label agrees with the real checker verdict
    for c <- sample do
      expected = if c.label == :positive, do: :ok, else: :error
      actual = case verdict(c) do
        :ok -> :ok
        {:error, _} -> :error
      end
      assert actual == expected, "label/verdict disagree for #{c.note}"
    end
  end
end
