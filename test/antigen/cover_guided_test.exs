defmodule Antigen.CoverGuidedTest do
  use ExUnit.Case, async: false   # :cover (+ :cover.reset) is node-wide global
  alias Antigen.{Cover, Triage, Challenge, Corpus}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, @nat, @nat}, body: body}

  # Reducible in both dimensions: droppable defs (g, h) + an S-tower body to shrink.
  defp both_dims_ch do
    tower = {:ctor, :S, [{:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}]}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [d(:f, tower), d(:g, {:ctor, :Z, []}), d(:h, {:ctor, :Z, []})], focus: [:f]},
      seed: 1
    )
  end

  test "delta/2 reports newly-covered lines and is empty when nothing new is hit" do
    Cover.with_cover([Antigen.CoverFixture], fn ->
      Antigen.CoverFixture.classify(5)          # hit the :pos branch
      s1 = Cover.covered_set([Antigen.CoverFixture])

      Antigen.CoverFixture.classify(-1)         # hit :neg — a NEW line
      d1 = Cover.delta(s1, [Antigen.CoverFixture])
      assert MapSet.size(d1) > 0
      assert Enum.all?(d1, fn {m, l} -> m == Antigen.CoverFixture and is_integer(l) end)

      s2 = Cover.covered_set([Antigen.CoverFixture])
      Antigen.CoverFixture.classify(-2)         # hit :neg again — nothing new
      d2 = Cover.delta(s2, [Antigen.CoverFixture])
      assert MapSet.size(d2) == 0
    end)
  end

  test "attribute/4 pins each challenge's novel coverage via per-challenge reset" do
    # Cover's cond line-attribution (confirmed by probe): classify(0) covers the
    # `n<0 -> :neg` head line 4 and the `n==0` guard line 6; classify(-1) covers
    # the :neg body line 5; classify(5) covers line 6 + the `true -> :pos` line 7.
    # So with a classify(0) baseline, -1 introduces line 5 and 5 introduces line 7 —
    # two distinct, non-empty novel sets. (A classify(5) baseline would make
    # classify(0) contribute nothing novel, since line 6 is already covered — a
    # correct result that just doesn't exercise the "distinct novel" assertion.)
    Cover.with_cover([Antigen.CoverFixture], fn ->
      Antigen.CoverFixture.classify(0)          # baseline: lines {4, 6}
      prev = Cover.covered_set([Antigen.CoverFixture])

      run = fn n -> Antigen.CoverFixture.classify(n) end
      attributed = Cover.attribute(prev, [-1, 5], run, [Antigen.CoverFixture])

      assert length(attributed) == 2
      assert Enum.all?(attributed, fn {_ch, novel} -> MapSet.size(novel) > 0 end)
      [{-1, neg_novel}, {5, pos_novel}] = attributed
      refute MapSet.equal?(neg_novel, pos_novel)
    end)
  end

  test "bank_interesting minimizes, banks to the edge corpus, and dedups by covered-line set" do
    ch = both_dims_ch()
    path = Path.join(System.tmp_dir!(), "edge_#{System.unique_integer([:positive])}.sexp")
    on_exit(fn -> File.rm_rf!(path) end)

    lines = MapSet.new([{Cure.Core.Eval, 107}, {Cure.Core.Eval, 108}])
    pred = fn _c -> true end   # always interesting → Triage shrinks maximally

    {status1, banked, seen1} = Cover.bank_interesting(ch, lines, path, MapSet.new(), pred, 500)
    assert status1 == :appended
    assert Triage.size(banked) < Triage.size(ch)      # actually minimized
    assert Enum.count(Corpus.stream(path)) == 1

    # a second, different challenge carrying the SAME covered-line set is NOT
    # re-banked — the in-memory seen_sets gate (not the on-disk key) enforces this.
    ch2 = %{ch | seed: 2}
    {status2, _b2, _seen2} = Cover.bank_interesting(ch2, lines, path, seen1, pred, 500)
    assert status2 == :skipped
    assert Enum.count(Corpus.stream(path)) == 1
  end

  test "refresh_seed_pool! merges a banked closed typed_term into the live crossover pool" do
    # A real closed :typed_term seed from the tracked corpus is guaranteed to
    # round-trip through Corpus encode/decode and pass SeedPool.load's closed?
    # filter — the only challenge shape this feedback path picks up.
    ch =
      Corpus.stream("test/antigen/seeds.sexp")
      |> Enum.find_value(fn
        {:ok, %Challenge{kind: :typed_term, payload: %{ctx: [], term: t}} = c} ->
          if Cure.Core.Term.closed?(t), do: c, else: nil

        _ ->
          nil
      end)

    assert ch, "fixture needs a closed :typed_term seed in test/antigen/seeds.sexp"
    type = ch.payload.type

    path = Path.join(System.tmp_dir!(), "edgepool_#{System.unique_integer([:positive])}.sexp")
    on_exit(fn -> File.rm_rf!(path) end)

    # pool BEFORE the bank does not know this type
    Process.put(:antigen_seed_pool, %{})
    refute Map.has_key?(Process.get(:antigen_seed_pool), type)

    # budget 0 = no shrink, so the banked challenge's recorded type is preserved
    {_st, _min, _seen} =
      Cover.bank_interesting(ch, [{Cure.Core.Eval, 99}], path, MapSet.new(), fn _ -> true end, 0)

    Cover.refresh_seed_pool!(path)

    pool = Process.get(:antigen_seed_pool)
    assert Map.has_key?(pool, type)   # crossover can now draw this type mid-run
    assert Antigen.Generators.SeedPool.pool_gen(pool, type) != :none
  end
end
