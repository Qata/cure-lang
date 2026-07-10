# Autopilot state — Migration Facility (task: migration-facility)

**Branch:** `autopilot/migration-facility` (worktree `.claude/worktrees/migration-facility`)
**Stage reached:** Stage 3 (Plan review) — **HALT: 15-pass ceiling without two consecutive clean passes.**
**Status:** Benign non-convergence — the review kept finding progressively smaller genuine issues and fixing them; pass 14 was clean (1 of 2), pass 15 found and fixed one more, resetting the counter. NOT stuck on an intractable defect. One focused convergence pass is owed.

## Artifacts committed

| Stage | Commit | Notes |
|---|---|---|
| Spec | `e6287f1` → hardened `bcea259` | 6-pass converged spec |
| Plan | `d0cd1a8` → hardened checkpoint `0126aa9` | 1511 lines; 15 passes of fixes; **not fully converged** |

## What the plan review fixed (high-value catches)

- Task 3 "missing node kinds" list had 9 phantom entries + 3 needing special handling → corrected to 15 verified entries.
- Missing built-in-type seeding for the uppercase-type-var rule (would have caused **catastrophic false positives on `Int`/`Bool`/etc.**).
- Wrong call sites / names (`Cli`→`CLI`, `Parser.parse` site), non-halting CLI entry point, bad fixtures.
- `git_guard/1` single-reason-per-batch contract couldn't represent mixed-reason batches → per-file `[{path, reason}]`.
- Added the spec-required static-exhaustiveness gate; extended corpus totality gate to include reparse+fixpoint.
- Four "reparses" assertions only called `Lexer.tokenize`, never `Parser.parse` → fixed with a `reparses?/2` helper.

## What blocked completion

The recursive-skeptical-review loop is designed to reach **two consecutive clean passes**; it hit the 15-pass safety ceiling first. This is a process ceiling, not a defect wall — the artifact is in good shape and one issue away from clean.

## Pending scope change (operator-fed mid-run, not yet applied)

**Third day-one seed rule: `@group(:x)` hoist** — relocate an in-body `@group(...)` decorator to directly above `mod` (idempotent), `:syntactic`. Supersedes the fragile line-regex script at `787a9745…/scratchpad/migrate_group.exs`. First *relocation/MOVE* rule → stresses `Trivia.carry/2` + blank-line policy. Must be folded into spec §5.5/§8 and added as a new plan task (with a comment-carry-across-move red test) before Stage 4.

## What it needs from the operator (decision)

The plan is a resilience-checkpoint commit but not converged, and a scope change (the `@group` rule) must be folded in regardless — which itself needs review. Options:

1. **(Recommended) Continue to close-out:** fold in the `@group` rule (spec + new plan task) + the §9 future-work note, then run ONE more focused recursive-skeptical-review pass over the amended plan to reach convergence, then proceed to Stage 4 execution. Rationale: non-convergence is benign, the operator is present, and the plan needs another edit+review cycle for `@group` anyway.
2. **Halt for manual review:** stop here; operator reviews the 1511-line plan by hand before any execution.

Awaiting operator go/no-go (operator was interactively present at halt time, so surfacing directly rather than only via push notification).
