# Coverage-Guided Fuzzing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Give Antigen real `:cover`-based code-coverage feedback over the Cure kernel, in two staged phases — (1) measure kernel coverage + report cold lines; (2) a coverage-guided loop that steers generation by new-edge yield.

**Architecture:** A new `Antigen.Cover` harness drives Erlang `:cover` around the existing `Runner.explore/1` campaign; `Antigen.CoverReport` renders the report. Phase 2 adds per-input coverage attribution, an edge-minimal corpus, a live-refreshed SeedPool, and edge-novelty generator reweighting — all in Antigen tooling, reusing `Mutation`/`Triage`/`Corpus`/`SeedPool` unchanged. Entry point is a new `cover` subcommand of `mix antigen`.

**Tech Stack:** Elixir/OTP `:cover`, `:beam_lib` (abstract_code for line→function), StreamData (only via `Antigen.Backend.StreamData`), ExUnit.

## Global Constraints

- **No TCB edits.** No changes to `Cure.Core.*` or `Cure.Elab.*`. Coverage is tooling; `:cover` instruments for measurement only (in-memory via `code:load_binary/3`, never writes `.beam`).
- **`:cover` is node/VM-global + serial.** One cover session per node. Every test file that starts/stops `:cover` MUST `use ExUnit.Case, async: false`. Never run the normal `mix test` under cover.
- **Always clean up cover.** Wrap campaigns in `try/after` so `:cover.stop/0` runs even on crash; instrumented modules must not leak into the rest of the VM.
- **StreamData quarantine.** Only `Antigen.Backend.StreamData` may reference `StreamData`. New generator/assay code must not.
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NEVER a `Co-Authored-By` trailer.
- **One build/test run at a time.** `MIX_ENV=test`, from the worktree root. Stay on `autopilot/antigen-tier-b`. No auto-merge.
- `@cover_modules = [Cure.Core.Kernel, Normalise, Conv, Eval, Quote, Inductive, Serialize, Certificate]` (verbatim from spec §Phase-1).

---

## File Structure

- **Create** `lib/antigen/cover.ex` — `Antigen.Cover`: `:cover` lifecycle, guard, campaign-under-cover, per-module analyse, cold-line extraction, (Phase 2) per-input delta + guided loop orchestration.
- **Create** `lib/antigen/cover_report.ex` — `Antigen.CoverReport`: line→function map via `:beam_lib`, deterministic markdown render.
- **Create** `test/support/cover_fixture.ex` — a tiny `Antigen.CoverFixture` module with known executable lines + a branch, used as the controlled target for Phase-1 unit tests (never the real kernel).
- **Modify** `lib/mix/tasks/antigen.ex` — add the `cover` mode (`["cover" | _]`) + `--out`/`--guided`/`--precise`/`--edge-corpus` switches.
- **Modify** `lib/antigen/runner.ex` — Phase 2: an edge-novelty reweighting hook usable by the guided loop, alongside (not replacing) `draw_biased`.
- **Create** `test/antigen/cover_test.exs`, `test/antigen/cover_report_test.exs`, `test/antigen/cover_guided_test.exs` — all `async: false`.
- **Reuse unchanged:** `Antigen.Generators.Mutation`, `Antigen.Triage`, `Antigen.Corpus`, `Antigen.Generators.SeedPool`, `Antigen.Report`.

**Interfaces produced (names later tasks rely on):**
- `Antigen.Cover.with_cover(modules, fun)` → runs `fun` with `modules` cover-compiled, guarantees `:cover.stop/0`; returns `fun`'s result.
- `Antigen.Cover.cover_compilable?(module)` → boolean (has `debug_info`).
- `Antigen.Cover.line_coverage(module)` → `%{covered: [line], cold: [line], total: n}` (from `:cover.analyse(module, :coverage, :line)`).
- `Antigen.Cover.run_report(opts)` → runs a campaign under cover, returns `%{module => line_coverage}`.
- `Antigen.CoverReport.render(coverage_map, fn_index)` → markdown string (deterministic).
- `Antigen.CoverReport.function_index(module)` → `%{line => {fun, arity}}` via `:beam_lib`.
- Phase 2: `Antigen.Cover.delta(prev_set, module)` → new lines; `Antigen.Cover.guided_loop(opts)`.

---

## PHASE 1 — Coverage measurement + report

### Task 1: `Antigen.Cover` lifecycle + cover-compilability guard

**Files:** Create `lib/antigen/cover.ex`, `test/support/cover_fixture.ex`, `test/antigen/cover_test.exs`.

- [ ] **Step 1: Create the fixture** `test/support/cover_fixture.ex`:

```elixir
defmodule Antigen.CoverFixture do
  @moduledoc false
  def classify(n) when is_integer(n) do
    cond do
      n < 0 -> :neg      # line A
      n == 0 -> :zero    # line B
      true -> :pos       # line C
    end
  end
end
```

(Ensure `test/support` is on the compile path — check `mix.exs` `elixirc_paths` for `:test`; if `test/support` isn't included, add it in this step and note it in the commit.)

- [ ] **Step 2: Write the failing test** (`test/antigen/cover_test.exs`):

```elixir
defmodule Antigen.CoverTest do
  use ExUnit.Case, async: false   # :cover is node-wide global
  alias Antigen.Cover

  test "cover_compilable? is true for a debug_info module, and with_cover cleans up" do
    assert Cover.cover_compilable?(Antigen.CoverFixture)
    refute :cover in :cover.modules()   # not instrumented before
    result = Cover.with_cover([Antigen.CoverFixture], fn ->
      Antigen.CoverFixture.classify(5)
      :ran
    end)
    assert result == :ran
    # cover fully stopped afterward — no leaked session
    assert catch_exit(:cover.modules()) != :normal or :cover.modules() == []
  end
end
```

> Confirm the exact post-stop assertion against OTP: after `:cover.stop/0`, `:cover.modules/0` raises (server down). Use `assert_raise`/`catch_exit` accordingly — the executor verifies the real behavior and pins the assertion; the intent is "no cover server left running."

- [ ] **Step 3: Run RED** — `MIX_ENV=test mix test test/antigen/cover_test.exs` → fails (module undefined).

- [ ] **Step 4: Implement** `lib/antigen/cover.ex`:

```elixir
defmodule Antigen.Cover do
  @moduledoc "Erlang :cover harness for kernel code coverage (Antigen tooling; no TCB changes)."

  @cover_modules [Cure.Core.Kernel, Cure.Core.Normalise, Cure.Core.Conv,
                  Cure.Core.Eval, Cure.Core.Quote, Cure.Core.Inductive,
                  Cure.Core.Serialize, Cure.Core.Certificate]
  def cover_modules, do: @cover_modules

  @doc "True if `module`'s beam carries debug_info (required by :cover.compile_beam)."
  def cover_compilable?(module) do
    case :code.which(module) do
      beam when is_list(beam) ->
        match?({:ok, {^module, [{:debug_info, _}]}}, :beam_lib.chunks(beam, [:debug_info])) or
          match?({:ok, _}, :beam_lib.chunks(beam, [:abstract_code]))
      _ -> false
    end
  end

  @doc "Run `fun` with `modules` cover-compiled; always :cover.stop afterward."
  def with_cover(modules, fun) do
    {:ok, _} = :cover.start()
    try do
      Enum.each(modules, fn m ->
        {:ok, ^m} = {:cover.compile_beam(m), m} |> normalize_compile(m)
      end)
      fun.()
    after
      :cover.stop()
    end
  end

  defp normalize_compile({{:ok, m}, _}, m), do: {:ok, m}
  defp normalize_compile({{:error, reason}, m}, m),
    do: raise("cover.compile_beam failed for #{inspect(m)}: #{inspect(reason)}")
end
```

> The executor pins `:cover.compile_beam/1`'s exact return shape (`{:ok, Module}` vs list) against OTP and simplifies `normalize_compile` accordingly. Keep the `try/after :cover.stop()` invariant.

- [ ] **Step 5: Run GREEN** — `MIX_ENV=test mix test test/antigen/cover_test.exs` → PASS.
- [ ] **Step 6: Commit** — `feat(antigen): :cover lifecycle harness + compilability guard`.

### Task 2: line coverage analyse + cold-line extraction

**Files:** Modify `lib/antigen/cover.ex`; extend `test/antigen/cover_test.exs`.

- [ ] **Step 1: Failing test** — run the fixture's `classify` under cover on inputs that hit only the `:pos` branch, assert `line_coverage` reports the `:neg`/`:zero` lines cold:

```elixir
  test "line_coverage reports covered and cold lines" do
    cov =
      Cover.with_cover([Antigen.CoverFixture], fn ->
        Antigen.CoverFixture.classify(5)   # hits :pos only
        Cover.line_coverage(Antigen.CoverFixture)
      end)
    assert cov.total > 0
    assert cov.cold != []                  # :neg / :zero never executed
    assert Enum.all?(cov.covered ++ cov.cold, &is_integer/1)
    assert length(cov.covered) + length(cov.cold) == cov.total
  end
```

- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `line_coverage/1` using `:cover.analyse(module, :coverage, :line)` — returns `{:ok, [{{Mod,Line},{Cov,NotCov}}]}`; `covered = lines where Cov==1`, `cold = lines where NotCov==1`. Note `line_coverage` must be called *inside* `with_cover` (before stop):

```elixir
  def line_coverage(module) do
    {:ok, pairs} = :cover.analyse(module, :coverage, :line)
    {cov, cold} =
      Enum.reduce(pairs, {[], []}, fn {{_m, line}, {c, _n}}, {yes, no} ->
        if c > 0, do: {[line | yes], no}, else: {yes, [line | no]}
      end)
    %{covered: Enum.sort(cov), cold: Enum.sort(cold), total: length(pairs)}
  end
```

> Pin `:cover.analyse/3`'s exact tuple shape against OTP (line 0 / non-executable lines may appear — filter `line == 0`).

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): line-coverage analyse + cold-line extraction`.

### Task 3: `Antigen.CoverReport` — line→function map + deterministic markdown

**Files:** Create `lib/antigen/cover_report.ex`, `test/antigen/cover_report_test.exs`.

- [ ] **Step 1: Failing test** — build a `function_index` for the fixture and assert cold lines render grouped under their function; assert render is deterministic (same input → byte-identical output, sorted, no timestamps):

```elixir
defmodule Antigen.CoverReportTest do
  use ExUnit.Case, async: false
  alias Antigen.CoverReport

  test "function_index maps lines to {fun, arity}" do
    idx = CoverReport.function_index(Antigen.CoverFixture)
    assert Enum.any?(idx, fn {_line, fa} -> fa == {:classify, 1} end)
  end

  test "render is deterministic and groups cold lines by function" do
    covmap = %{Antigen.CoverFixture => %{covered: [5], cold: [3, 4], total: 3}}
    idx = CoverReport.function_index(Antigen.CoverFixture)
    out1 = CoverReport.render(covmap, %{Antigen.CoverFixture => idx})
    out2 = CoverReport.render(covmap, %{Antigen.CoverFixture => idx})
    assert out1 == out2
    assert out1 =~ "classify/1"
  end
end
```

- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `function_index/1` via `:beam_lib.chunks(beam, [:abstract_code])` → walk the abstract forms, mapping each function's clause line spans to `{name, arity}`. Implement `render/2`: a per-module summary table (module, covered/total, %) sorted by module name, then a "Cold lines" section grouping each module's cold lines under their enclosing `fun/arity` (unknown → `:module-level`). No timestamps in the body.

> The abstract_code walk: each `{:function, _line, name, arity, clauses}` form carries clause/line annotations; map every line in the function's span to `{name, arity}`. The executor confirms the abstract_code shape against `:beam_lib` docs.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): coverage report renderer (line→function, deterministic markdown)`.

### Task 4: `mix antigen cover` subcommand

**Files:** Modify `lib/mix/tasks/antigen.ex`; extend a mix-task test (or `test/antigen/cover_test.exs`).

- [ ] **Step 1: Failing test** — assert `mode` resolution routes `["cover"]` to a cover run and that `run_report/1` produces a `%{module => coverage}` map over the real `@cover_modules` (small `--count`), writing a report to a tmp `--out`. Keep it `async: false` and small.

- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `Antigen.Cover.run_report(opts)` — `with_cover(@cover_modules, fn -> run a campaign (Runner.explore with opts[:count]/gen) then Map.new(@cover_modules, &{&1, line_coverage(&1)}) end)`, then render + write to `opts[:out]`. Add `mode = :cover` dispatch in `Mix.Tasks.Antigen.run/1` (`match?(["cover" | _], rest)`), parse `--out`, call `Cover.run_report`, print a one-line summary. Add `out`/`guided`/`precise`/`edge_corpus` to `@switches`.

- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): mix antigen cover subcommand (Phase 1 report)`.

### Task 5: Phase 1 verification (real kernel)

- [ ] **Step 1:** `MIX_ENV=test mix antigen cover --count 500 --out /tmp/kcov.md` → produces a report over the real kernel modules; eyeball that cold lines look plausible (e.g. rarely-hit error branches).
- [ ] **Step 2:** `MIX_ENV=test mix test` → full suite still green (cover left no residue; new tests `async: false`). Confirm `:cover.modules()` server is down after the task.
- [ ] **Step 3: Commit** any report artifact intentionally kept, else none. Phase 1 complete.

---

## PHASE 2 — Coverage-guided loop

### Task 6: per-input coverage delta (batch-gate + precise re-attribution)

**Files:** Modify `lib/antigen/cover.ex`; `test/antigen/cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — with the fixture cover-compiled, snapshot the accumulated covered set, run an input hitting a new line, assert `delta/2` returns exactly that new line; run an input hitting only already-covered lines, assert `delta/2` is empty. (`async: false`.)
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `covered_set(modules)` (union of `line_coverage` covered, tagged `{module, line}`) and `delta(prev_set, modules)` = `covered_set - prev_set`. Implement the **batch-gate/precise** pair: `round_delta(prev, modules)` (one analyse) and, when non-empty, `attribute(prev, challenges, run_fun, modules)` which `:cover.reset()`s and re-runs each challenge individually to find which caused new lines. Note `:cover.reset/0` clears counters node-wide — only valid inside a `with_cover` block and incompatible with concurrent cover use (already guarded by `async: false` + the serial mode).
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): per-input coverage delta (batch-gate + precise attribution)`.

### Task 7: interesting-input edge-minimal corpus

**Files:** Modify `lib/antigen/cover.ex`; extend `cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — feed a challenge that hits a new edge; assert it's banked to a tmp edge-corpus (via `Corpus.append`), minimized first via `Triage.minimize` (assert banked size ≤ original), and deduped by covered-line set (a second challenge with the same covered set is not re-banked).
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `bank_interesting(challenge, new_lines, edge_corpus_path, seen_sets)` — if `MapSet.new(new_lines)` not in `seen_sets`: `Triage.minimize(challenge, pred, budget)` where `pred` re-runs the challenge under cover and checks it still hits ≥1 of `new_lines`; `Corpus.append(edge_corpus_path, min_challenge, dedup_key)`; return the updated `seen_sets`. Default path `test/antigen/edge_corpus.sexp`.
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): edge-minimal interesting-input corpus (Triage-minimized, set-deduped)`.

### Task 8: SeedPool live-refresh feedback

**Files:** Modify `lib/antigen/cover.ex`; extend `cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — assert that after `bank_interesting`, the guided loop re-`Process.put(:antigen_seed_pool, ...)` a pool that now includes the banked term's type key (so `gnat`'s crossover can draw it within the same run). Assert the pool before the bank lacked it and after includes it.
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `refresh_seed_pool!(edge_corpus_path)` — `SeedPool.load(edge_corpus_path)` (or in-memory merge of the newly banked seed) and `Process.put(:antigen_seed_pool, pool)`. Call it after each `bank_interesting`. This is orchestration in `Antigen.Cover`; `SeedPool` source is unchanged (spec §Phase-2 mechanism note).
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): live SeedPool refresh so crossover sees banked edges mid-run`.

### Task 9: edge-novelty generator reweighting

**Files:** Modify `lib/antigen/runner.ex`; `test/antigen/runner_test.exs` (async: false if it touches shared state).

- [ ] **Step 1: Failing test** — a pure unit test of the reweight function: given per-group new-edge yields, assert groups with higher new-edge yield get proportionally higher weight (parallel to the existing health-based `reweight`, but keyed on edge yield). No `:cover` needed for this unit (feed synthetic yields).
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `reweight_by_edges(weights, group_table, edge_yields)` in `runner.ex` — mirrors the existing `reweight/3` shape but uses edge-yield stamps. Keep it additive: the default `explore`/`draw_biased` path is untouched; the guided loop opts into this reweighter.
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): edge-novelty generator reweighting (guided-mode bias)`.

### Task 10: guided loop orchestration + jackpot coverage-delta

**Files:** Modify `lib/antigen/cover.ex` (+ `runner.ex` if the loop lives there); extend `cover_guided_test.exs`.

- [ ] **Step 1: Failing test** — run a short guided loop over the fixture (or a small kernel campaign); assert it (a) terminates on plateau (K rounds no new edge), (b) grows the edge-corpus monotonically, and (c) when a challenge both hits a new edge AND violates (use a stub assay that violates on a marked input), the single `Report.write_infection` call carries a coverage-delta field in its `health` map (not a second report).
- [ ] **Step 2: RED.**
- [ ] **Step 3: Implement** `guided_loop(opts)` — the draw→run-under-cover→delta→(bank+refresh+reweight | discard)→repeat loop with a plateau counter; thread coverage delta into the existing `write_infection(dir, c, detail, health)` call by adding `:coverage_delta` to the `health` map. Reuse `Runner.explore`'s per-challenge assay dispatch; do not fork it — factor the shared step if needed, keeping the non-guided path byte-identical.
- [ ] **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): coverage-guided loop + jackpot coverage-delta in infection report`.

### Task 11: `mix antigen cover --guided` wiring

**Files:** Modify `lib/mix/tasks/antigen.ex`; extend the mix-task test.

- [ ] **Step 1: Failing test** — assert `["cover"]` + `--guided` routes to `guided_loop`, `--precise` sets the precise flag, `--edge-corpus PATH` overrides the corpus path.
- [ ] **Step 2: RED.** **Step 3:** wire the flags into `Cover.guided_loop(opts)`. **Step 4: GREEN.** **Step 5: Commit** — `feat(antigen): mix antigen cover --guided/--precise/--edge-corpus wiring`.

### Task 12: Phase 2 verification

- [ ] **Step 1:** `MIX_ENV=test mix antigen cover --guided --count 2000 --out /tmp/kcov2.md` → runs the guided loop, banks an edge-corpus, produces a report. Compare kernel coverage % vs. the Phase-1 unguided run at equal budget (spec Risk #3: guided should reach ≥ unguided coverage; log the delta — if not measurably better, record the finding, do NOT silently claim success).
- [ ] **Step 2:** `MIX_ENV=test mix test` → full suite green; `:cover` server down afterward; no StreamData token in new non-backend files (`architecture_test.exs` still green).
- [ ] **Step 3:** Restore/keep `test/antigen/edge_corpus.sexp` per the standing corpus-expansion policy (intentional expansion; commit separately if it grew). Commit any kept report.

---

## Self-review (against spec)

- **Phase 1 (measure+report)** → Tasks 1–5 (lifecycle+guard, analyse+cold, report+beam_lib fn-map, mix subcommand, verify). ✓
- **Phase 2 (guided loop)** → Tasks 6–12 (delta batch/precise, edge-minimal corpus, SeedPool live-refresh, edge reweight, loop+jackpot, wiring, verify). ✓
- **Spec Risk #1 (cover-compilable/debug_info)** → Task 1 `cover_compilable?` guard. ✓
- **Spec Risk #2 (batch/precise cost)** → Task 6 nested model + Task 12 quantifies both regimes. ✓
- **Spec Risk #3 (indirect feedback weakest link)** → Task 12 Step 1 explicitly measures guided-vs-unguided and records a finding if not better. ✓
- **Spec Risk #4 (determinism)** → Task 3 deterministic render test. ✓
- **Spec Risk #5 (line→function needs beam_lib)** → Task 3 `function_index` via abstract_code. ✓
- **No-TCB-edits / cover cleanup / async:false / quarantine** → Global Constraints + every cover test `async: false` + Task 12 architecture_test check. ✓
- **No placeholders:** each task shows red test + impl sketch; API shapes flagged "executor pins against OTP" only where the exact OTP tuple must be confirmed at the keyboard (`:cover.analyse`, `:cover.compile_beam`, `:beam_lib` abstract_code) — never for Antigen-internal reuse APIs, which are pinned (`Runner.explore`, `Report.write_infection/4`, `SeedPool.load/1`, `Corpus.append/3`).
