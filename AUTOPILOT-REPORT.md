# Autopilot completion report — Antigen Tier A

**Branch:** `autopilot/cure-dependent-types-frp` (worktree `.claude/worktrees/cure-dependent-types-frp`)
**Status:** ✅ Complete — ready for operator review & merge (not auto-merged).
**Full suite:** `mix test` → **2100 passed, 0 excluded, 0 failures**. Working tree git-clean after the run.
**Update:** the operator directed fixing the hole; the mutual-recursion soundness hole is now **fixed** in `Cure.Core.Certificate` (see §Hole fixed). The corpus-replay invariant test now runs by default and is green.

## What was built

The schema-directed half of **Antigen**, a property-based metatheory-testing engine for the Cure kernel. It catches the confirmed mutual-recursion totality hole **two independent ways** with zero dependence on a general dependent-term generator.

## Stage-by-stage outcome

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | (prior session) Tier-A spec written | `a30c68f`, umbrella `382fd1c` |
| 1 — Spec review (Sonnet 5, recursive-skeptical-review) | Converged 8 passes; caught a vacuous `conv(t,t)` assay design + 9 other issues, fixed inline | `a18b30d` |
| 2 — Plan (inline) | 15-task, 2-phase plan written against **verified** kernel signatures (mapped via 2 Explore agents + direct `conv.ex` read) | `76f701e` |
| 3 — Plan review (Sonnet 5) | Converged 5 passes; fixed `fold_depth` vs. its own test, corpus `scaffold` carry-through, `System.trap_signal(:sigint)` impossibility, `cli/0` vs `project/0` | `80dd1f6` |
| 4 — Execute (inline TDD, Opus, one build at a time) | 15 tasks, red→green→commit each | `ba3574f` … `5bf42c9` (15 commits) |
| 5 — Verify | Full suite 2097 passed / 1 excluded; git-clean | — |

## Success criteria (spec §2) — all met

1. ✅ `mix antigen` generates mutual-recursion groups, the certifier wrongly certifies them (`totality/diverging` infection), result deduped, written to `tmp/antigen/`, appended to the antibody corpus, self-terminating. (Seeding run: 49 infections → 2 deduped antibodies.)
2. ✅ `reflexivity-as-normalization` independently flags the downstream consequence: `conv(t, t')` exceeds its fixed δ-unfold fuel → `{:non_normalizing, :conv_exceeded_fuel}`.
3. ✅ `totality/terminating` and `positivity` pass on known-good and fail on injected known-bad (both directions exercised).
4. ✅ `mix test` statically replays both corpora, reports every failing entry non-fail-fast, never mutates them (git-clean confirmed).
5. ✅ `mix antigen generate` harvests into the seed bank; per-record atomic append means SIGINT loses nothing already banked.
6. ✅ Architecture test green: nothing under `Antigen.Generators.*` / `Antigen.Assays.*` references `StreamData`.

**Sequencing:** the hole was caught live first (criteria 1–2 via live antibodies), then **fixed** at the operator's direction — so criteria 1–2 are now evidenced exactly as the spec's sequencing note's post-fix branch describes: the assays correctly report *no* violation, and the generator self-tests + never-pruned corpus antibodies stand as the enduring proof + regression guard.

## Key facts / notable engineering

- **The hole, reproduced by construction:** `f = λx. g x`, `g = λx. f x` (Dec→Dec). `Certificate.calls?/2` matches only a function's own name, so `terminating?(:f, body_f)` returns `true` immediately — verified empirically against the real certifier before baking the generator.
- **Additive TCB edit:** `Cure.Core.Conv.conv_within?/6` bounds total δ-unfolds via a process-local counter consulted only when set; the existing `conv?/5` path is behaviorally unchanged (existing conv suite still green).
- **Corpus is generator-independent:** two committed, never-pruned, C2-serialized stores (`test/antigen/corpus.sexp` antibodies, `test/antigen/seeds.sexp` seed bank). A record envelope composes `Serialize.encode/1` over each `Term` piece + a `scaffold=` metadata channel.
- **Replay atom-safety fix (found by the replayer itself):** decoding a committed record in a fresh process that never ran a generator was crashing on `String.to_existing_atom`; fixed by force-interning the closed kind/label/name set in `Antigen.Challenge` (`@known_atoms`).

## Hole fixed (per operator instruction: "leave the test red and just fix the hole")

Rather than exclude the red replay test, the mutual-recursion soundness hole is **fixed**:

- **`Cure.Core.Certificate.terminating?/3`** is now env-aware and rejects a def that sits on a **mutual cycle** — following calls through sibling globals, if a path returns to the def, it is not certified. Single-def structural recursion is unchanged; non-cyclic helper calls still certify regardless of certification order (verified against `TotalityClosure`'s arbitrary-order closure). `Kernel.validate_certificate` threads `env` through. This matches the module's own long-stated intent ("mutual recursion … soundly rejected") — previously aspirational, now enforced.
- **Red→green proof:** `test/cure/core/certificate_test.exs` gained a test that the cycle `f→g→f` is rejected (`{:error, :not_total}`), plus a guard that a non-cyclic helper (`use_id → id`) still certifies. Both green.
- **The `@tag :antigen_live_hole` exclusion is gone** — `test_helper.exs` no longer excludes anything; the corpus-replay invariant test runs in the default suite and is green.
- **Antigen tests updated to post-fix reality** (spec §2 sequencing note): the totality/reflexivity assays now correctly report *no* violation on the (now-safe) kernel; the enduring proof of detection is the **generator self-tests** (label-correct by construction; `refute Certificate.terminating?(mutual)`), the **fuel mechanism test** (via a manual `Env.certify`, isolating the Conv bound from the certifier), and the **two never-pruned corpus antibodies** — permanent regression guards that go red again if the hole is ever reintroduced.

**No follow-up decision needed.** The kernel is sound against this hole and the suite is fully green.

## Not done (out of scope, as designed)

- **Tier B** (the general dependent-term generator + differential assays) — its own future spec; it will feed the same seed bank.
- **Fixing** the hole — a separate spec that consumes these antibodies.
