defmodule Antigen.CorpusReplayTest do
  @moduledoc """
  The permanent regression harness (spec §7, §8 replayer). Decodes the two
  committed, never-pruned stores and re-runs each entry's assay **through the
  kernel** — read-only, non-fail-fast, never mutating the files (so `mix test`
  stays git-clean).

  The mutual-recursion hole has since been **fixed** in `Cure.Core.Certificate`
  (mutual-cycle detection), so every committed entry now satisfies its invariant
  and the invariant-check test below is GREEN. The two antibodies remain in the
  corpus as **permanent regression guards** (never pruned, spec §7.1): if the hole
  is ever reintroduced, `totality/diverging` and `reflexivity` replay to a
  violation again and this test goes red.
  """
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Assays}

  @corpus "test/antigen/corpus.sexp"
  @seeds "test/antigen/seeds.sexp"

  @registry %{
    "stub" => Assays.Stub,
    "totality/diverging" => Assays.Totality,
    "totality/terminating" => Assays.Totality,
    "positivity" => Assays.Positivity,
    "reflexivity" => Assays.Reflexivity,
    "indexed/case" => Assays.Indexed
  }

  test "both committed corpora decode without error (structural integrity)" do
    for path <- [@corpus, @seeds], File.exists?(path) do
      results = Runner.replay([path], @registry)
      refute results == []
      assert Enum.all?(results, fn r -> not match?({:decode_error, _, _}, r.verdict) end)
    end
  end

  test "replay does not mutate the committed corpora (git-clean for CI)" do
    for path <- [@corpus, @seeds], File.exists?(path) do
      before = File.read!(path)
      Runner.replay([path], @registry)
      assert File.read!(path) == before
    end
  end

  test "every committed entry satisfies its assay invariant (regression guard)" do
    failing =
      Runner.replay([@corpus, @seeds], @registry)
      |> Enum.reject(fn r -> r.verdict == :ok end)

    assert failing == [],
           "#{length(failing)} committed entr(y/ies) fail their invariant — the " <>
             "mutual-recursion hole may have regressed: " <>
             inspect(Enum.map(failing, & &1.verdict))
  end
end
