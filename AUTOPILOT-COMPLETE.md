# Autopilot completion report — stdlib-test-isolation

**Branch:** `autopilot/stdlib-test-isolation` (cut from `feature/idris-parity` HEAD)
**Date:** 2026-07-17
**Status:** ✅ Complete — awaiting operator review & merge. **NOT auto-merged.**

## Goal

Eliminate the flaky/slow behavior of the Cure compiler test suite caused by
producer tests clobbering the global BEAM code-table slot for canonical stdlib
modules, **without** splitting the single suite. Load-and-stick the canonical
stdlib once at startup; namespace emitter-verifying producers under a per-test
module prefix; simplify pure consumers to call the sticky canonical.

## Outcome

Historical clobber flake eliminated. Full suite green and deterministic across
seeds, and roughly 4 min instead of the old ~6 min:

- Stage 6 gate (seed 0): **4447 passed, 1 skipped, 0 failed**, 196.6 s, Antigen 318/318.
- Stage 5 full run (seed 42): 4447 passed, 1 skipped, 0 failed, Antigen 318/318.
- Earlier determinism gate: green at seeds 0 and 4242.

## The five components

- **C1** — load + stick canonical stdlib at suite startup (`test/test_helper.exs`).
- **C2** — namespace emitter-verifying producers via a module-name prefix threaded
  through `Cure.Elab.Emit` (`:prefix` / `:local_owners`; `remote_target/2` reroute).
- **C3** — simplify pure consumers to resolve the sticky canonical.
- **C4** — golden byte-compare tests kept un-namespaced.
- **C5** — flip isolated files to `async: true`.

## Per-stage commits

- Stage 2 plan: `3b1058e4`.
- Stage 3 plan review (Sonnet 5): `070457c6`.
- Stage 4 implementation (Opus, TDD, per task):
  - `64fc7ec4` sticky-tolerance precondition
  - `031a5f12` C1 load+stick at startup
  - `4677f9b8` re-stick after preload purge sites
  - `d2c8690f` C2 emit prefix + local_owners threading
  - `6f2c7b87` C2 prefixed isolation + delegation guarantees test
  - `8f3338ef` C2 namespace set_dependent_run producer
  - `9a2df1d8` C3 stdlib_test calls sticky canonical directly
  - `a992500d` C5 iter_test async
  - `b86617b1` C1 guard scoped to `Cure.Std.*`
  - `23e07006` C2 dependent-runtime firewall under prefix (plan-gap producer)
  - `232bf299` C3 vec codegen resolves sticky canonical (plan-gap consumer)
- Stage 5 code review (Sonnet 5, converged after 2 clean passes):
  - `f13d4aed` fix(preload): skip already-resident modules to silence sticky-dir log spam (+ red test)
  - `68b48221` fix(test): correct vacuous refute anchor in emit_prefix_test.exs
  - `67448240` fix(test): correct vacuous sticky-tolerance assertion in preload_sticky_test.exs

## Plan-gap corrections (found during the determinism gate, not in the original plan)

1. `dependent_emit_runtime_test.exs` — an emitter-verifying producer the plan
   missed; migrated to the C2 prefix (`23e07006`).
2. `dependent_vec_codegen_test.exs` — test 3 re-compiled canonical Vector/Nat/
   Bounded; the compiler front-end has no prefix threading, so simplified to
   resolve the sticky canonical (`232bf299`). Coverage preserved: inline `VecCg`
   (test 1) still exercises the full compiler path.

## Stage 5 findings (all fixed, red-test-first)

Three defects, all test-integrity / operational-noise rather than logic bugs in
the emitter — the C1/C2/C3 production code held up:

- Preload retry log spam against sticky modules (278 spam lines measured).
- Two vacuous assertions that could not fail (proven by mutation) in
  `emit_prefix_test.exs` and `preload_sticky_test.exs`.

## Follow-up items (not blockers)

- `set_dependent_run_test.exs` retains `async: false`; could move to `async: true` later.

## Investigated and rejected: parallel `mix test` partitioning

Prompted by the new ~4-min baseline, a multi-partition `mix test` runner was
prototyped and benchmarked end-to-end (compile + run, seed 0, 8-core host):

| Config | Wall | vs serial |
|--------|------|-----------|
| Serial `mix test` | 236 s | — |
| 2 partitions | 221 s | −6 % |
| 4 partitions | 214 s | −9 % |

All configurations produced identical, correct results (4447 passed, 1 skipped;
partitions aggregate exactly). The speedup is marginal and does not scale, for
two structural reasons: (1) ExUnit's `--partitions` splits *execution* only, so
every partition still compiles all 663 test files (redundant compile paid N×);
(2) it buckets modules by name-hash, blind to duration, so a few heavy modules
(Antigen property suites, OTP metatheory) clump into one partition and set the
wall floor (122 s of 214 s at N=4). Capping each VM's scheduler count made no
difference — the bottleneck is compile-redundancy + imbalance, not CPU
oversubscription. **Decision:** not worth overriding the `test` alias for a <10 %
gain (and the risk to IDE line-runs / `mix test <file>` / `--failed`). Dropped.
The only approach that could beat this — disjoint file-list splitting (compile
each file once, greedy-balance by measured duration) — was scoped but not built.
