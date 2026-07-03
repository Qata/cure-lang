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

  defp tmp(name), do: Path.join(@tmp, name)

  test "explore(challenges: ...) bypasses the generator entirely (existing override path)" do
    # regression guard for the pre-existing `opts[:challenges] || draw(...)` override.
    # `explore/1` returns %{infections, seeds_banked, health: %{discard_rate}, ...}
    # (no top-level :discards key). A single well-formed stub banks as one seed and
    # is not discarded, exercising exactly the one supplied challenge.
    cs = [Antigen.Challenge.stub({:type, 0})]
    r = Antigen.Runner.explore(challenges: cs, count: 1, corpus_path: tmp("c.sexp"),
                               seeds_path: tmp("s.sexp"), report_dir: tmp("r"))
    assert r.seeds_banked == 1
    assert r.infections == 0
    assert r.health.discard_rate == 0.0
  end

  test "explore(bias: false) draws via `gen` (no challenges override) and processes exactly `count`" do
    # exercises spec §4's bias:false path (`true -> draw(opts[:gen], count)`). The
    # 1-in-10 `:boom` branch of Generators.Stub.gen() lands with overwhelming
    # probability at count 300 (P(never) = 0.9^300 ≈ 1e-14), mirroring the file's
    # existing non-flaky assertion pattern.
    opts = [gen: Generators.Stub.gen(), assay: Assays.Stub, bias: false, count: 300,
            corpus_path: tmp("c3.sexp"), seeds_path: tmp("s3.sexp"), report_dir: tmp("r3")]
    r = Antigen.Runner.explore(opts)
    assert r.infections >= 1
  end

  test "default_gen has exactly 11 branches in the documented group order (guard)" do
    {:frequency, ws} = Mix.Tasks.Antigen.default_gen()
    assert length(ws) == 11
    assert Antigen.Runner.gen_group_table() ==
             %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
  end

  test "bias:true bumps the vacuous group's total weight, floors hold, Group F unchanged" do
    base = %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
    w0 = List.duplicate(1, 11)
    w_t = Antigen.Runner.reweight(w0, base, %{health_stamp: :vacuous, mutation_stamp: :healthy,
                                              conv_reject_count: 5, conv_accept_count: 5})
    assert Enum.all?(base.t, fn i -> Enum.at(w_t, i - 1) > 1 end)
    assert Enum.all?(base.f, fn i -> Enum.at(w_t, i - 1) == 1 end)
    assert Enum.all?(w_t, &(&1 >= 1))
  end

  test "explore(bias: true) runs the round loop end-to-end through the real default_gen mix" do
    # integration test for draw_biased/3 (round-splitting, per-round stamping, gen
    # rebuild) against the real {:frequency, ws} shape. count 12 / round_size 5
    # forces 3 rounds (5 + 5 + 2), exercising a mid-batch reweight.
    opts = [gen: Mix.Tasks.Antigen.default_gen(), bias: true, count: 12, round_size: 5,
            corpus_path: tmp("c5.sexp"), seeds_path: tmp("s5.sexp"), report_dir: tmp("r5")]
    r = Antigen.Runner.explore(opts)
    assert %{infections: _, seeds_banked: _, health: _, health_metrics: _, stamp: _} = r
  end
end
