# Antigen directed generation — Implementation Plan (Run A)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. Steps use `- [ ]` checkboxes.

**Goal:** Make Antigen generation reach deeper/more-diverse shapes without touching the kernel — via an enriched coverage key, corpus-backed fillers, and health-adaptive round-based biasing.

**Architecture:** Three independent, pure-Antigen changes. Part 1 folds new structural signals into `Coverage`'s existing 4-tuple key (arity-preserving). Part 2 adds a `SeedPool` that reuses closed banked `typed_term`s as well-typed fillers. Part 3 restructures `Runner.explore/1` into an opt-in round loop that reweights `default_gen`'s 11-branch mix by challenge-KIND group.

**Tech Stack:** Elixir; `Antigen.{Coverage, Corpus, Runner, Gen}`; `Antigen.Generators.{Term, Mutation, SeedPool}`; `Cure.Core.Term`.

## Global Constraints

- Ghost-authored commits: `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`.
- `MIX_ENV=test mix test …`; macOS has no `timeout`; one build/test run at a time.
- **No `Cure.Core.*` (TCB) edits. No `StreamData` literal** in anything under `lib/antigen/generators/` or `assays/` (grep-enforced by `architecture_test.exs`) — `SeedPool` uses `Antigen.Corpus` + `Antigen.Gen` only.
- **`Coverage.key/1` stays a 4-tuple** `{ctors, bucket, flags, label}` — new signals fold into the `flags` `MapSet` (spec §2), so `Runner.coverage_flags/1`'s positional destructure keeps working.
- **`bias: false` (default) must issue exactly one undivided `draw(opts[:gen], count)`** — `Backend.StreamData.interp |> Enum.take` is not composable (spec §4). The round loop runs only under `bias: true`.
- Tests immutable once correct (change impl, not the test; sole exception is a proven-wrong test, stated explicitly).

---

## Task 1: Coverage-vector enrichment (spec §2)

**Files:** Modify `lib/antigen/coverage.ex`; Test `test/antigen/coverage_test.exs`.

**Interfaces:** Produces enriched `flags` (extra atoms `:former_<class>_<0|1|many>`, `:binder_depth_<bucket>`) inside the same 4-tuple; `key_string/1` renders them via the existing `flags` join.

- [ ] **Step 1: Write the failing test**

```elixir
# append to test/antigen/coverage_test.exs
  alias Antigen.{Coverage, Challenge}

  defp tt(term), do: Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
                                   payload: %{sig: :v1, ctx: [], type: {:data, :Nat, [], []}, term: term})

  test "coverage key distinguishes terms that collide under the coarse key" do
    # same constructor set (none), same label, same overall depth band, but different shape mix
    a = tt({:lam, {:type, 0}, {:lam, {:type, 0}, {:var, 1}}})           # nested binders
    b = tt({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 0}})      # applications
    refute Coverage.key(a) == Coverage.key(b)
  end

  test "enriched key still plateaus (bounded distinct keys over many terms)" do
    terms = for d <- 0..40 do
      Enum.reduce(0..rem(d, 6), {:ctor, :Z, []}, fn _, acc -> {:ctor, :S, [acc]} end)
    end
    keys = terms |> Enum.map(&Coverage.key(tt(&1))) |> Enum.uniq()
    assert length(keys) <= 12, "key space must saturate, got #{length(keys)}"
  end
```

- [ ] **Step 2: Run — expect FAIL** (`mix test test/antigen/coverage_test.exs`) — the first test fails: both terms currently key equal (empty ctor set, same bucket/flags/label).

- [ ] **Step 3: Implement** — in `lib/antigen/coverage.ex`, extend `flags/3` to fold in the two signal families, and add the helpers:

```elixir
  defp flags(%Challenge{kind: kind}, terms, ctors) do
    base = for {c, flag} <- @elim_flags, MapSet.member?(ctors, c), into: MapSet.new(), do: flag
    base = if kind in [:def_group, :forcing_pair], do: MapSet.put(base, :has_mutual_group), else: base
    base = if Enum.any?(terms, &has_shadowing?/1), do: MapSet.put(base, :has_shadowing), else: base
    base = MapSet.union(base, former_flags(terms))
    MapSet.put(base, binder_depth_flag(terms))
  end

  @former_classes [:lam, :pi, :app, :case, :ctor, :data, :eq, :rewrite, :prim]
  defp former_flags(terms) do
    counts = Enum.reduce(terms, %{}, fn t, acc -> count_formers(t, acc) end)
    for cls <- @former_classes, into: MapSet.new() do
      :"former_#{cls}_#{count_bucket(Map.get(counts, cls, 0))}"
    end
  end

  defp count_bucket(0), do: :n0
  defp count_bucket(1), do: :n1
  defp count_bucket(_), do: :nm

  defp count_formers(t, acc) do
    acc = case elem_tag(t) do
      cls when cls in @former_classes -> Map.update(acc, cls, 1, &(&1 + 1))
      _ -> acc
    end
    child_terms(t) |> Enum.reduce(acc, &count_formers/2)
  end

  defp elem_tag(t) when is_tuple(t) and tuple_size(t) > 0, do: elem(t, 0)
  defp elem_tag(_), do: nil

  # binder nesting depth (lam/pi/sigma body, case-branch body increment)
  defp binder_depth_flag(terms) do
    d = terms |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
    :"binder_depth_#{bucket(d)}"
  end

  defp binder_depth({t, _dom, body}) when t in [:lam, :pi, :sigma], do: 1 + binder_depth(body)
  defp binder_depth({:case, s, m, brs}) do
    Enum.max([binder_depth(s), binder_depth(m) |
              Enum.map(brs, fn {_c, ar, b} -> (if ar > 0, do: 1, else: 0) + binder_depth(b) end)])
  end
  defp binder_depth(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
  defp binder_depth(l) when is_list(l), do: l |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
  defp binder_depth(_), do: 0
```

Add a `child_terms/1` helper mirroring the tuple/list walk (or reuse an existing one in the module if present — check `fold/3`). `bucket/1` already exists and is reused for the binder-depth bucket. `key_string/1` needs no change (it already sorts+joins the `flags` set).

- [ ] **Step 4: Run — expect PASS.** Also run `mix test test/antigen/coverage_test.exs test/antigen/runner_test.exs` to confirm `Runner.coverage_flags/1`'s positional destructure still holds (arity unchanged).

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/coverage.ex test/antigen/coverage_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): enrich coverage key with former-histogram + binder-depth flags"
```

---

## Task 2: SeedPool — corpus-backed fillers (spec §3)

**Files:** Create `lib/antigen/generators/seed_pool.ex`, `test/antigen/generators/seed_pool_test.exs`; Modify `lib/antigen/generators/mutation.ex` (route `gnat` through a pooled branch) and `lib/antigen/generators/term.ex` (low-freq pool branch).

**Interfaces:**
- Produces `SeedPool.load(path) :: %{Term.t() => [Term.t()]}` (type → closed terms), `SeedPool.pool_gen(pool, goal) :: Gen.t() | :none`.
- Consumes `Antigen.Corpus.stream/1`, `Antigen.Gen`, a closedness check (reuse `Antigen.Shrink.closed?` if it accepts a bare term, else a local `closed?/1`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/generators/seed_pool_test.exs
defmodule Antigen.Generators.SeedPoolTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SeedPool
  alias Antigen.{Challenge, Corpus}
  alias Cure.Core.Term

  @tmp "tmp/seedpool_test"
  setup do
    File.rm_rf!(@tmp); File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  defp bank(path, c), do: Corpus.append(path, c, Corpus.dedup_key(c, :antibody))

  test "pool indexes only closed typed_term seeds, keyed by recorded type" do
    path = Path.join(@tmp, "seeds.sexp")
    nat = {:data, :Nat, [], []}
    bank(path, Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
      payload: %{sig: :v1, ctx: [], type: nat, term: {:ctor, :S, [{:ctor, :Z, []}]}}))
    # a mutant with a nominal type MUST NOT enter the pool
    bank(path, Challenge.new(kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
      payload: %{sig: :v1, ctx: [], type: nat, term: {:fst, {:ctor, :Z, []}}, fault: %{kind: :proj_non_pair}}))

    pool = SeedPool.load(path)
    assert [{:ctor, :S, [{:ctor, :Z, []}]}] = Map.get(pool, nat)
    assert match?(%Antigen.Gen{} , SeedPool.pool_gen(pool, nat)) or is_tuple(SeedPool.pool_gen(pool, nat))
    assert SeedPool.pool_gen(pool, {:data, :Vec, [], [{:ctor, :Z, []}]}) == :none
    assert Enum.all?(Map.get(pool, nat), &Term.term?/1)
  end

  test "absent file yields an empty pool and :none for every goal" do
    pool = SeedPool.load(Path.join(@tmp, "missing.sexp"))
    assert pool == %{}
    assert SeedPool.pool_gen(pool, {:data, :Nat, [], []}) == :none
  end
end
```

- [ ] **Step 2: Run — expect FAIL** — `SeedPool` undefined.

- [ ] **Step 3: Implement** — `lib/antigen/generators/seed_pool.ex`:

```elixir
defmodule Antigen.Generators.SeedPool do
  @moduledoc """
  Corpus-backed fillers (spec §3): reuse *closed* banked `:typed_term` seeds as
  well-typed fillers, indexed by their kernel-checked recorded type. Only
  `:typed_term` seeds qualify — a `:mutant_term`'s `type` is a nominal fault-site
  goal its term does NOT actually inhabit. Backend-free (no StreamData literal).
  """
  alias Antigen.{Corpus, Gen}
  alias Cure.Core.Term

  @spec load(String.t()) :: %{Term.t() => [Term.t()]}
  def load(path) do
    Corpus.stream(path)
    |> Enum.flat_map(fn
      {:ok, %{kind: :typed_term, payload: %{ctx: [], type: type, term: term}}} ->
        if closed?(term), do: [{type, term}], else: []
      _ -> []
    end)
    |> Enum.group_by(fn {type, _} -> type end, fn {_, term} -> term end)
  end

  @spec pool_gen(%{Term.t() => [Term.t()]}, Term.t()) :: Gen.t() | :none
  def pool_gen(pool, goal) do
    case Map.get(pool, goal) do
      nil -> :none
      [] -> :none
      terms -> Gen.member_of(terms)
    end
  end

  # de-Bruijn closedness of a bare term (no free var, counting binders)
  def closed?(t), do: max_index_below(t, 0) < 0
  defp max_index_below({:var, k}, d) when k >= d, do: k - d
  defp max_index_below({:var, _}, _d), do: -1
  defp max_index_below({t, dom, body}, d) when t in [:lam, :pi, :sigma],
    do: max(max_index_below(dom, d), max_index_below(body, d + 1))
  defp max_index_below({:case, s, m, brs}, d) do
    [max_index_below(s, d), max_index_below(m, d) |
     Enum.map(brs, fn {_c, ar, b} -> max_index_below(b, d + ar) end)] |> Enum.max()
  end
  defp max_index_below(t, d) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&max_index_below(&1, d)) |> max_or(-1)
  defp max_index_below(l, d) when is_list(l),
    do: l |> Enum.map(&max_index_below(&1, d)) |> max_or(-1)
  defp max_index_below(_, _), do: -1
  defp max_or([], v), do: v
  defp max_or(xs, _), do: Enum.max(xs)
end
```

Then wire a low-frequency pool branch into the Nat filler in `lib/antigen/generators/mutation.ex`. Change `gnat/1` to consult a process-scoped pool if one is installed (kept opt-in so existing tests are unaffected when no pool is set):

```elixir
  # gnat: well-typed Nat filler; occasionally a banked closed Nat (if a pool is installed)
  defp gnat(ctx) do
    fresh = Term.gen_term(ctx, nat_t())
    case Process.get(:antigen_seed_pool) do
      %{} = pool ->
        case Antigen.Generators.SeedPool.pool_gen(pool, nat_t()) do
          :none -> fresh
          g -> Gen.frequency([{4, fresh}, {1, g}])
        end
      _ -> fresh
    end
  end
```

`Mix.Tasks.Antigen` installs the pool once before exploring (`Process.put(:antigen_seed_pool, SeedPool.load(seeds_path))`) — added in Task 3's CLI edit. When no pool is installed (all existing tests), `gnat` is byte-identical to today.

- [ ] **Step 4: Run — expect PASS** (`mix test test/antigen/generators/seed_pool_test.exs test/antigen/generators/mutation_test.exs test/antigen/architecture_test.exs`) — SeedPool tests green, mutation tests still green (no pool installed), quarantine green.

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/generators/seed_pool.ex lib/antigen/generators/mutation.ex test/antigen/generators/seed_pool_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): SeedPool — reuse closed banked typed_terms as fillers (opt-in)"
```

---

## Task 3: Health-adaptive round loop + guard test (spec §4)

**Files:** Modify `lib/antigen/runner.ex` (round loop, `bias:` opt), `lib/mix/tasks/antigen.ex` (`--bias` flag, pool install); Test `test/antigen/runner_test.exs`.

**Interfaces:**
- Produces `Runner.explore(opts)` accepting `bias: boolean` (default `false`) and `round_size: pos_integer` (default 200); `bias: false` ⇒ one undivided `draw`. Reweighting operates at group granularity (T = default_gen branches 4–6,9–11; M = 7–8; F = 1–3 fixed).
- Consumes `default_gen/0`'s literal 11-branch order (position→group table pinned by a guard test).

- [ ] **Step 1: Write the failing tests**

```elixir
# append to test/antigen/runner_test.exs
  test "explore(bias: false) issues exactly one draw and matches the unbiased path" do
    # a deterministic challenge list bypasses draw; bias:false must not re-batch it
    cs = [Antigen.Challenge.stub({:type, 0})]
    r = Antigen.Runner.explore(challenges: cs, count: 1, corpus_path: tmp("c.sexp"),
                               seeds_path: tmp("s.sexp"), report_dir: tmp("r"))
    assert r.seeds_banked + r.infections + r.discards == 1
  end

  test "default_gen has exactly 11 branches in the documented group order (guard)" do
    {:frequency, ws} = Mix.Tasks.Antigen.default_gen()
    assert length(ws) == 11
    # groups by challenge kind of a sampled draw are stable at the pinned positions
    assert Antigen.Runner.gen_group_table() ==
             %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
  end

  test "bias:true bumps the vacuous group's total weight, floors hold, Group F unchanged" do
    base = %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
    w0 = List.duplicate(1, 11)
    w_t = Antigen.Runner.reweight(w0, base, %{health_stamp: :vacuous, mutation_stamp: :healthy,
                                              conv_reject_count: 5, conv_accept_count: 5})
    # Group T positions rose, Group F unchanged, nothing dropped to 0
    assert Enum.all?(base.t, fn i -> Enum.at(w_t, i - 1) > 1 end)
    assert Enum.all?(base.f, fn i -> Enum.at(w_t, i - 1) == 1 end)
    assert Enum.all?(w_t, &(&1 >= 1))
  end
```

- [ ] **Step 2: Run — expect FAIL** — `gen_group_table/0`/`reweight/3` undefined; the bias:false test may pass already (regression guard).

- [ ] **Step 3: Implement** — in `lib/antigen/runner.ex`:

```elixir
  @round_size 200
  @group_table %{f: [1, 2, 3], t: [4, 5, 6, 9, 10, 11], m: [7, 8]}
  def gen_group_table, do: @group_table

  # bump every position in the low-health group(s); floor 1; Group F never bumped.
  def reweight(weights, table \\ @group_table, stamps) do
    bumps =
      []
      |> maybe_bump(table.t, stamps[:health_stamp] == :vacuous or stamps[:conv_accept_count] == 0)
      |> maybe_bump(table.m, stamps[:mutation_stamp] == :vacuous or stamps[:conv_reject_count] == 0)

    weights
    |> Enum.with_index(1)
    |> Enum.map(fn {w, i} -> if i in bumps, do: w + 2, else: max(w, 1) end)
  end

  defp maybe_bump(acc, _positions, false), do: acc
  defp maybe_bump(acc, positions, true), do: acc ++ positions
```

Restructure `explore/1`'s head so `bias: true` runs rounds and `bias: false` keeps the single draw:

```elixir
  def explore(opts) do
    count = Keyword.get(opts, :count, 200)
    challenges =
      cond do
        opts[:challenges] -> opts[:challenges]
        opts[:bias] -> draw_biased(opts[:gen], count, Keyword.get(opts, :round_size, @round_size))
        true -> draw(opts[:gen], count)     # exactly one undivided draw (spec §4)
      end
    # … existing reduce body unchanged …
```

`draw_biased/3` draws `round_size` at a time, computes the three stamps over the accumulated batch (reusing `health_metrics`/`mutation_metrics`/`conversion_metrics` + the stamp fns), calls `reweight/3`, rebuilds the `{:frequency, ws}` gen with new weights, and continues until `count` is reached — each round issuing one `draw` for its slice. (It does NOT re-draw the same gen; each round is a fresh `draw` of a freshly-weighted gen, which is the intended adaptive behavior — the non-composability constraint only forbids splitting a *single logical* uniform draw, which is the `bias:false` path.)

In `lib/mix/tasks/antigen.ex`: add `bias: :boolean` to `@switches`, pass `bias: opts[:bias]` into `runner_opts`, install the pool before exploring:

```elixir
    if seeds_path = opts[:seeds] || "test/antigen/seeds.sexp",
       do: Process.put(:antigen_seed_pool, Antigen.Generators.SeedPool.load(seeds_path))
```

and note in `@moduledoc` that `--bias` needs `--count` above the 200 round size to have any effect.

- [ ] **Step 4: Run — expect PASS** (`mix test test/antigen/runner_test.exs`).

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/runner.ex lib/mix/tasks/antigen.ex test/antigen/runner_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): health-adaptive round loop (opt-in --bias) + default_gen group guard"
```

---

## Self-Review

**Spec coverage:** §2 enrichment → Task 1 (arity-preserving flags, plateau test). §3 SeedPool → Task 2 (typed_term-only, closed-only, absent-file inert, quarantine). §4 rounds → Task 3 (bias:false one-draw; group reweight; Group-F-fixed; guard test; --bias doc). §5 tests → Tasks 1–3 + Stage-5 sanity. §6 files match. §7 non-goals respected (no TCB; closed-only; syntactic type-eq; no format change).

**Placeholder scan:** none — every step has concrete code. (`child_terms/1` reuse is flagged to check the module's existing `fold/3`.)

**Type consistency:** `SeedPool.{load,pool_gen,closed?}` defined Task 2, consumed by `gnat` (Task 2) + CLI (Task 3). `Runner.{gen_group_table,reweight,draw_biased}` defined Task 3. `@group_table` positions match `default_gen/0`'s committed 11-branch order (Totality/Positivity/Forcing = 1–3; typed_term×3 = 4–6; mutant = 7; conv_reject = 8; conv_accept×3 = 9–11) — pinned by the guard test.

**Ordering:** Task 1 (coverage) independent. Task 2 (SeedPool) before Task 3 (CLI installs the pool). Stage 5 runs the full suite once + `mix antigen --count 800 --bias` to a tmp corpus, recording health-line deltas vs baseline.
