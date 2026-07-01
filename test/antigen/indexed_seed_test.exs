defmodule Antigen.IndexedSeedTest do
  @moduledoc """
  Banks the indexed/case vertical's permanent stores (spec §7) and guards that
  every banked record replays through the kernel to `:ok`. Idempotent: on a fresh
  checkout the committed records are already present, so `Corpus.append/3` finds
  them via its `seen?` dedup and writes nothing (keeping `mix test` git-clean).
  Run in isolation first to generate the files, then commit them.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Runner, Assays}
  alias Antigen.Generators.Indexed

  @seeds "test/antigen/seeds.sexp"
  @corpus "test/antigen/corpus.sexp"

  # Confirmed 4.1 regression guard: a Dec case with a foreign `MkFoo` (Foo) branch.
  # Post-fix the kernel rejects it, so it replays :ok; if the family-scoping fix
  # regresses, it replays {:wrongly_accepted, _} and the invariant test goes red.
  @antibodies [Indexed.branch_family(:ill_typed)]

  # Known-good-behavior seeds: every OTHER indexed/case challenge the kernel
  # currently handles correctly. `refinement(:well_typed)` is intentionally absent
  # — it exposes a documented incompleteness (wrongly rejected), so it does not
  # replay :ok and must not be banked as a "known-good" seed.
  @seed_candidates [
    Indexed.branch_family(:well_typed),
    Indexed.coverage(:well_typed),
    Indexed.coverage(:ill_typed),
    Indexed.refinement(:ill_typed),
    Indexed.motive_wf(:well_typed),
    Indexed.motive_wf(:ill_typed)
  ]

  test "indexed/case antibodies + seeds are banked and every one replays :ok" do
    for a <- @antibodies, do: Corpus.append(@corpus, a, Corpus.dedup_key(a, :antibody))

    for s <- @seed_candidates, Assays.Indexed.run(s) == :ok do
      Corpus.append(@seeds, s, Corpus.dedup_key(s, :seed))
    end

    reg = %{"indexed/case" => Assays.Indexed}
    results = Runner.replay([@corpus, @seeds], reg)

    indexed = Enum.filter(results, fn r -> match?(%Antigen.Challenge{assay: "indexed/case"}, r.entry) end)
    refute indexed == []
    assert Enum.all?(indexed, fn r -> r.verdict == :ok end),
           "indexed/case replay produced a non-:ok verdict: " <>
             inspect(indexed |> Enum.reject(&(&1.verdict == :ok)) |> Enum.map(& &1.verdict))
  end
end
