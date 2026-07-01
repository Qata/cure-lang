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
end
