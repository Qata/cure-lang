# Autopilot state — Migration Facility (task: migration-facility)

**Branch:** `autopilot/migration-facility` (worktree `.claude/worktrees/migration-facility`)
**Stage reached:** Stage 4 (Execute) — in progress. (Stage 3 halt RESOLVED.)
**Status:** Operator chose "continue to close-out" (option A). The `@group` third seed rule + §9 future-work were folded into spec (`981b5ed`) and plan (`a7aabe8`); a focused convergence review over the new content reached two consecutive clean passes with zero findings. Plan treated as converged; proceeding to inline TDD execution on Opus.

## Stage 3 halt (historical) — resolved

The plan review hit the 15-pass ceiling one issue short of two-consecutive-clean (benign — kept finding progressively smaller genuine issues and fixing them). Operator authorized close-out rather than manual review. Convergence pass confirmed the additions are sound.

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

## Resolution

Operator chose **A (continue to close-out)**. Done: `@group` rule folded into spec §5.5/§8 + §1/§6/§7, §9 future-work added (`981b5ed`); Task 9b added to plan with cross-refs (`a7aabe8`); focused convergence review clean (2/2, zero findings). Now executing Stage 4 (inline TDD, Opus). If a plan defect surfaces during execution, TDD catches it and it is fixed inline per executing-plans.
