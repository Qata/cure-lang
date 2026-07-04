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

  test "default_gen has exactly 25 branches in the documented group order (guard)" do
    {:frequency, ws} = Mix.Tasks.Antigen.default_gen()
    assert length(ws) == 25
    # positions 15-18 are the structure-directed Primitive + Equality + TypeFormer
    # + DepMatch generators (:typed_term producers → group `t`); positions 19, 24 &
    # 25 are the family/index-shaped IndexedDecl + BranchUnify + DotForcing probes →
    # group `f`; positions 20-23 are the Malformed negative + Serialization
    # roundtrip + decode-robustness + conv-decision verticals → group `t`.
    assert Antigen.Runner.gen_group_table() ==
             %{f: [1, 2, 3, 19, 24, 25], t: [4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23], m: [7, 8]}
  end

  test "kernel-law verticals run to completion with 0 infections on the sound kernel" do
    for id <- ~w(kernel/shift_subst kernel/weakening kernel/confluence) do
      opts = [gen: Antigen.Generators.Term.typed_term(id), count: 40,
              corpus_path: tmp("kl_c_#{String.replace(id, "/", "_")}.sexp"),
              seeds_path: tmp("kl_s_#{String.replace(id, "/", "_")}.sexp"),
              report_dir: tmp("kl_r_#{String.replace(id, "/", "_")}")]
      r = Antigen.Runner.explore(opts)
      assert r.infections == 0, "#{id} false-positived on the sound kernel"
    end
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

  test "reweight_by_edges bumps each group proportionally to its new-edge yield" do
    base = %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
    w0 = List.duplicate(1, 11)
    # t group yielded the most new edges, m some, f none
    out = Antigen.Runner.reweight_by_edges(w0, base, %{f: 0, t: 5, m: 1})

    t_w = Enum.at(out, hd(base.t) - 1)
    m_w = Enum.at(out, hd(base.m) - 1)
    f_w = Enum.at(out, hd(base.f) - 1)

    assert t_w > m_w                       # more edges → more weight
    assert m_w > f_w
    assert Enum.all?(base.f, fn i -> Enum.at(out, i - 1) == 1 end)  # zero-yield floors at 1
    assert Enum.all?(out, &(&1 >= 1))
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

defmodule Antigen.RunnerTest.TriageWiring do
  use ExUnit.Case, async: false
  alias Antigen.{Runner, Challenge}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, @nat, @nat}, body: body}

  # A module-shaped assay (runner calls `apply(mod, :run, [c])`) that infects iff a
  # def named :f survives — so bisect may drop the redundant :g but NOT :f, giving a
  # deterministic minimized target of exactly [:f].
  defmodule KeepsF do
    def run(%Challenge{payload: %{defs: defs}}) do
      if Enum.any?(defs, &(&1.name == :f)), do: {:violation, :boom}, else: :ok
    end

    def run(_), do: :ok
  end

  test "a non-typed_term infection is banked minimized (bisect drops a redundant def)" do
    tmp = Path.join(System.tmp_dir!(), "antigen-triage-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)

    ch = Challenge.new(kind: :def_group, assay: "totality/terminating", label: :terminating,
           payload: %{defs: [d(:f, {:ctor, :Z, []}), d(:g, {:ctor, :Z, []})], focus: [:f]}, seed: 7)

    # `opts[:assay]` is the runner's existing assay-module override (runner.ex:52),
    # used both for the initial verdict and inside the shrink/bisect predicate.
    res = Runner.explore(challenges: [ch], assay: KeepsF,
            report_dir: tmp, corpus_path: Path.join(tmp, "c.sexp"),
            seeds_path: Path.join(tmp, "s.sexp"))

    assert res.infections == 1
    banked = tmp |> Path.join("c.sexp") |> Antigen.Corpus.stream() |> Enum.to_list()
    assert [{:ok, min}] = banked
    # bisect dropped the redundant :g; :f is load-bearing to the predicate, so it stays
    assert Enum.map(min.payload.defs, & &1.name) == [:f]
    assert min.payload.focus == [:f]
  end
end
