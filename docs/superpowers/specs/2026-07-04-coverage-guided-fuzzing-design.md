# Coverage-Guided Fuzzing for the Cure Kernel — Design

**Date:** 2026-07-04
**Status:** Design approved (operator: "both, staged … we want the real thing, get it made").
**Branch:** `autopilot/antigen-tier-b` (stay on it — no new worktree per sub-feature).

## Goal

Give Antigen **real code-coverage feedback over the trusted kernel** (`Cure.Core.*`),
the capability libFuzzer provides and Antigen currently lacks. Today's "coverage"
is a *semantic* feature-key (`Antigen.Coverage.key/1` → `{ctors, depth-bucket,
flags, label}`) used for corpus dedup + a health/bias loop; there is **no
instrumentation of the kernel's actual code paths**, so we cannot answer "which
clauses of `Kernel`/`Normalise`/`Conv` has a campaign exercised, and which are
cold." This sub-project adds that, in two stages.

## Non-goals

- **No TCB edits.** Coverage is measurement infrastructure; it lives in Antigen /
  tooling. `:cover` instruments modules for measurement but does not alter kernel
  semantics — the assays still run the real kernel logic. (Consistent with spec §6
  "no `Cure.*` edits in assays"; this is a new tooling layer, not an assay.)
- **Not replacing the semantic coverage key.** The feature-key stays (it drives
  dedup + health). Code coverage is an *additional*, orthogonal signal.
- **No concurrency with the normal test suite.** `:cover` is process-global and
  slow; coverage runs are a dedicated, serial mode, never mixed into `mix test`.
- **v1 granularity is line-level** (what Erlang `:cover` gives natively).
  Clause/branch-level is a documented future stretch, not v1.

## Architecture

Two phases, staged. Phase 1 ships and is useful on its own; Phase 2 reuses Phase
1's harness as its feedback signal.

### Phase 1 — Coverage measurement + report

A `:cover`-based harness (`Antigen.Cover`, new module) that:

1. **Instruments a fixed TCB module set** — `Cure.Core.Kernel`, `Normalise`,
   `Conv`, `Eval`, `Quote`, `Inductive`, `Serialize`. (The list is a single
   `@cover_modules` constant, reviewed against what the assays actually call.)
2. **Runs a campaign** — reuse `Runner.explore/1`'s generation + assay loop
   (unchanged) with cover active around it.
3. **Analyses** line-level coverage via `:cover.analyse(mod, :coverage, :line)`
   after the campaign, and computes per-module covered/total + the set of **cold
   lines** (0 calls).
4. **Emits a report** — a deterministic markdown report
   (`docs/superpowers/reports/antigen-kernel-coverage.md` or a `--out` path):
   per-module summary table + a "cold clauses" section (grouped by function).

**Isolation & lifecycle:** `:cover.start` → `:cover.compile_beam`/`compile` the
module set → run → `:cover.analyse` → `:cover.stop`. Handle the process-global,
serial nature explicitly (one cover run at a time). Cover-compiled modules are
slower; that's acceptable for a dedicated coverage campaign. The normal suite is
never run under cover.

**Entry point:** `mix antigen cover [--count N | --budget Nm] [--out PATH]`
(a new subcommand of the existing `mix antigen` task, alongside `generate`).

### Phase 2 — Coverage-guided loop (libFuzzer-style)

Turn new-coverage into the **feedback signal** that steers generation.

1. **Per-input coverage delta.** Capture the coverage set a challenge triggers.
   Two modes:
   - **Precise** (`:cover.reset` + run + `:cover.analyse` per challenge) — exact
     per-input edge set, slower.
   - **Batch** — accumulate over a round, attribute new edges to the round; cheaper,
     coarser. Default to batch with a `--precise` opt-in.
2. **Interesting-input corpus.** An input that hits ≥1 new kernel line is
   "interesting" → banked to an **edge-minimal corpus** (keyed by its
   covered-line set, deduped via the existing `Antigen.Corpus`). This is the
   libFuzzer corpus model: keep the smallest input covering each new edge (the
   existing `Triage.minimize` provides the "smallest" step).
3. **Feedback into generation.** Antigen's generator is *generative* (mode-directed
   term synthesis), not byte-mutation, so the guided step derives new candidates
   from interesting corpus inputs by **reusing existing machinery**: the mutation
   operators (`Generators.Mutation`), `deepen`, and the seed-pool crossover
   (`gnat`/`SeedPool` already reuse banked closed terms). Edge-novelty replaces
   the health-metric as the round bias signal (parallel to today's `draw_biased`
   reweighting, but keyed on new-edge yield per generator group).
4. **The loop:** draw (generative + corpus-derived) → run under cover → new-edge
   delta → if new: bank + boost that lineage's weight; else discard → repeat until
   budget or plateau (K rounds with no new edge).
5. **Jackpot integration:** an input that hits new coverage AND trips an assay is a
   soundness bug in previously-cold kernel code — reported with both its coverage
   delta and the infection (reuse `Report.write_infection`).

## Components / files (indicative — the plan pins exact paths)

- **New:** `lib/antigen/cover.ex` — the `:cover` harness (instrument, run,
  analyse, cold-line extraction). Pure tooling.
- **New:** `lib/antigen/cover_report.ex` — render the coverage report (markdown).
- **Modify:** `lib/mix/tasks/antigen.ex` — add the `cover` subcommand + Phase-2
  `--guided` flag.
- **Modify:** `lib/antigen/runner.ex` — Phase 2: an edge-novelty bias hook
  alongside the existing health-based `draw_biased` (guarded behind the guided
  mode; the default explore path is unchanged).
- **Reuse (no change):** `Generators.Mutation`, `Triage`, `Corpus`, `SeedPool`.

## Testing strategy

- **Phase 1:** unit-test `Antigen.Cover` on a *tiny* controlled target — instrument
  a known module, run inputs that hit a known subset of lines, assert the analysed
  cold set matches. Assert report rendering is deterministic. Assert cover is
  stopped/cleaned up even on error (no leaked cover state into the suite).
- **Phase 2:** unit-test the interesting-input decision (an input with a new edge
  is banked; one with no new edge is discarded), the edge-minimal dedup, and the
  bias reweighting (a generator group that yields new edges gains weight). Test the
  jackpot path (new-edge + violation → infection report carries both).
- **Isolation guard:** a test asserting a cover run leaves `:cover` stopped and the
  module set restored (so the normal async suite is unaffected).
- **No coverage run inside the normal `mix test`** — the harness tests use a
  minimal fixture module, not the full kernel campaign.

## Risks / open questions (for spec-review to harden)

1. **`:cover` + already-loaded/compiled modules.** The kernel modules are compiled
   into `_build`; `:cover.compile_beam` re-instruments from the `.beam`. Confirm
   the module set is `:cover`-compilable and that instrumentation doesn't perturb
   escript/AtomVM builds (it shouldn't — cover is a test-time concern, separate mode).
2. **Per-input cost.** Precise mode's per-challenge `reset`/`analyse` may dominate
   runtime; the batch default mitigates. Quantify in the plan.
3. **Generative vs. mutation feedback.** The guided loop leans on corpus-derived
   mutation; validate that mutating an *interesting* input actually explores nearby
   kernel edges (vs. the generative baseline). If weak, the fallback is
   feature-key-correlated biasing (steer the generative mix toward semantic
   features observed to correlate with new edges).
4. **Determinism.** Coverage is deterministic given inputs + seeds; the report must
   be stable (sorted, no timestamps in the diffable body). The guided loop records
   seeds for replay.
5. **Cold-line → clause mapping.** Line-level cold lines should be grouped by
   enclosing function for a readable report; clause-level is future work.

## Staging

- **Phase 1** is independently landable: instrument + campaign + report. Delivers
  immediate value (kernel cold-spot visibility) with zero generator changes.
- **Phase 2** builds on Phase 1's harness: the guided loop + interesting corpus +
  edge-novelty bias. The plan will split each phase into TDD tasks.
