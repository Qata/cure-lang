defmodule Antigen.MutationMetaTest do
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Corpus, Challenge}

  @seeds_path "test/antigen/seeds.sexp"
  test "banked :mutant_term seed corpus meets the diversity floor (static replay)" do
    banked =
      Corpus.stream(@seeds_path)
      |> Enum.flat_map(fn
        {:ok, %Challenge{kind: :mutant_term} = c} -> [c]
        _ -> []
      end)

    assert banked != [], "no :mutant_term seeds banked yet"
    m = Runner.mutation_metrics(banked)
    assert m.reason_diversity >= 5, "banked reason_diversity #{m.reason_diversity} below floor"
  end
end
