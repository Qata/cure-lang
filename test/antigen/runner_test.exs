defmodule Antigen.RunnerTest do
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Challenge, Generators, Assays}

  @tmp "tmp/antigen_runner_test"
  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)

    [
      opts: [
        gen: Generators.Stub.gen(),
        assay: Assays.Stub,
        corpus_path: Path.join(@tmp, "corpus.sexp"),
        seeds_path: Path.join(@tmp, "seeds.sexp"),
        report_dir: @tmp,
        count: 300
      ]
    ]
  end

  test "explore harvests the planted infection, banks it, and keeps going", %{opts: opts} do
    result = Runner.explore(opts)
    assert result.infections >= 1
    assert File.exists?(opts[:corpus_path])
    assert Enum.any?(File.stream!(opts[:corpus_path]), &(&1 =~ "assay=stub"))
  end

  test "explore banks coverage-novel seeds and dedups repeats", %{opts: opts} do
    Runner.explore(opts)
    lines = File.stream!(opts[:seeds_path]) |> Enum.to_list()
    # no duplicate seed lines
    assert length(lines) == (lines |> Enum.uniq() |> length())
  end

  test "generate harvests seeds without running any assay (no reports written)", %{opts: opts} do
    %{seeds_banked: n} = Runner.generate(opts)
    assert n >= 1
    # assays skipped ⇒ no infection reports
    refute File.exists?(Path.join(@tmp, "latest.txt"))
  end

  test "replay re-runs the assay through the kernel and reports the planted violation", %{opts: opts} do
    boom = Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:global, :boom}}, seed: 1)
    Antigen.Corpus.append(opts[:corpus_path], boom, Antigen.Corpus.dedup_key(boom, :antibody))
    results = Runner.replay([opts[:corpus_path]], %{"stub" => Assays.Stub})
    assert Enum.any?(results, &match?(%{verdict: {:violation, _}}, &1))
  end
end
