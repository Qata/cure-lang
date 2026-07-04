defmodule Antigen.ReachPinTest do
  @moduledoc """
  Banks + replays `test/antigen/reach.sexp` (pre-port banking spec D2): challenges
  whose ground-truth label the checker does not yet achieve. Each entry's replay
  is pinned to its DOCUMENTED current violation, so drift in EITHER direction is
  loud: an accidental acceptance (permissiveness appearing without P1) and an
  accidental new rejection shape both fail this test.

  MIGRATION CONTRACT (spec D2): the port run that achieves an entry (P1 for all
  initial entries) appends the byte-identical record line to corpus.sexp, removes
  it here, and deletes the matching pin below — in the same commit. Records are
  never edited in place.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Assays}
  alias Antigen.Generators.Totality

  @reach "test/antigen/reach.sexp"

  # `wellfounded_ackermann` was ACHIEVED by #14 (size-change + reconstruct-equal):
  # its byte-identical record migrated from reach.sexp into corpus.sexp and its pin
  # was deleted here, per the MIGRATION CONTRACT above. The two remaining pins are
  # MUTUAL groups, still conservatively rejected (cross-function SCT out of scope).
  @pins [
    Totality.wellfounded_even_odd(),
    Totality.wellfounded_permuted_pair()
  ]

  # keyed by focus — the pinned CURRENT verdict for each banked entry
  @expected %{
    [:even, :odd] => {:violation, {:wrongly_rejected, [:even, :odd]}},
    [:f, :g] => {:violation, {:wrongly_rejected, [:f, :g]}}
  }

  test "reach pins are banked and replay to their documented conservative rejection" do
    for c <- @pins, do: Corpus.append(@reach, c, Corpus.dedup_key(c, :antibody))

    decoded = @reach |> Corpus.stream() |> Enum.map(fn {:ok, c} -> c end)
    assert length(decoded) == map_size(@expected)

    for c <- decoded do
      assert Assays.Totality.run(c) == Map.fetch!(@expected, c.payload.focus),
             "reach pin #{inspect(c.payload.focus)} drifted from its pinned verdict"
    end
  end
end
