# Autopilot Completion Report — Cure Editions

**Branch:** `autopilot/editions` (worktree `.claude/worktrees/editions`)
**Status:** ✅ Complete — full suite green, ready for review & merge. **NOT auto-merged.**
**Final gate:** `MIX_ENV=test mix test` → **3817 passed, 0 failures** (3 doctests, 3814 tests; baseline before this work was 3778). Antigen shape-coverage 309/309.

> The previous run's report (kernel-parity-batch) that this file replaces remains in git history.

## What shipped

A Rust-style **editions** system layered over Cure's migration facility (spec scope "C"): editions gate the parser keyword set and carry per-rule provenance; `cure migrate` rewrites both keyword and stdlib changes across an edition boundary and can stamp the new edition; there is no edition-conditional stdlib resolver (renamed names error with a fix-hint). Edition identity is a calendar-year string; precedence is file `@edition("YYYY")` pragma > `Cure.toml` `[project].edition` > compiler default. Editions begin at "2026"; `proto`→`interface` is the first forward deprecation (`enforced_in: nil`).

## Stage-by-stage outcome

| Stage | Outcome | Commit(s) |
|-------|---------|-----------|
| 0 — Brainstorm + spec | Design approved by operator; spec written | `1a3dc93` |
| 1 — Spec review (Sonnet, recursive-skeptical) | Hardened to convergence | `fe97bc2` |
| 2 — Plan (writing-plans) | 13-task plan across 7 phases | `426fcf9` |
| 3 — Plan review (Sonnet, recursive-skeptical) | Hardened to convergence | `bf5b606` |
| 4 — Execute (Opus, TDD) | 12 task commits (Tasks 3+4 atomic), all green | `0fb93db` … `813093d` |
| 5 — Verify + report | Full suite green; this report; notify | — |

## Task commits (Stage 4)

- `0fb93db` Task 1 — `Cure.Edition` identity, ordering, validation
- `d5ac15a` Task 2 — `resolve/1` precedence + `Cure.toml [project].edition`
- `309bcc6` Tasks 3+4 (atomic) — `tier`/`since`/`enforced_in` provenance replaces `tolerate_safe?` on `Rule`; 5 rules re-tagged
- `b2dca93` Task 5 — edition-derived keyword set in the lexer
- `d2f00bf` Task 6 — thread `:edition` through the parser; enforce `@edition` placement
- `ed2014e` Task 7 — `run_to_fixpoint/2` with reparse verify + `@max_passes 8` backstop
- `30ff52c` Task 8 — monotone-rewrite property gate over the 44-file stdlib corpus
- `9231a9a` Task 9 — `proto`/`impl` → `interface`/`implementation` rule (first `retires_keywords` rule) + `parse_impl` `for_type` fix
- `efba21f` Task 10 — edition-crossing rule selection + lossless `Cure.toml` edition writer
- `2be6ab5` Task 11 — edition-aware two-phase `cure migrate` (fixpoint rewrite + edition bump, `--strict`, `--edition`)
- `813093d` Task 12 — Antigen coverage probes for the edition keyword-set + migrate fixpoint (manifest 307→309)
- Task 13 — full-suite gate: no fixups needed, no commit (tree already green)

## Notable in-flight corrections (subagents caught real defects)

1. **Task 7** — the plan's convergence check `new_ast == ast` was provably wrong: paired flip rules cancel to identity, so pass 1 looks converged. Fixed with a per-step `rewrote?` flag (converge only when AST unchanged AND no rule rewrote), so pure `:warn` rules don't loop forever.
2. **Task 9** — the plan pinned `proto→interface` as tier `:machine`, but `:machine` folds rewrites into `cure build`, which would reroute the stdlib's `Ord`/`Show` to the dependent pipeline that cannot yet compile them (the `<`/`<>` blockers), reddening every build. Downgraded to `:review` (source untouched under `:safe_only`; `cure migrate` still rewrites), with a promote-to-`:machine` note. Also added `Trivia.carry/2` to preserve doc-comments the naive rewrite dropped (caught by the monotone gate).
3. **Task 12** — the plan expected a raised Antigen floor, but `Cure.Edition`/`Cure.Migrate` aren't among the 8 cover-compiled kernel modules, so the floor is unaffected. Probes are still legitimate soundness assertions gated by the CoverManifest; source trusted over the plan.

Every deviation trusted real source over a plan snippet and is documented in its commit; no behavioral test was weakened (the only immutable-test edits were plan-sanctioned: Tasks 3+4 fixture keys and Task 11's stale `--strict` pin, both re-asserting the new contract).

## Ghost-writing constraint

All 15 run commits authored as `Made In Heaven <madeinheaven@madeinheaven.com>`; a trailer scan across all bodies found **zero** `Co-Authored-By` / `Claude-Session` / "Generated with" trailers.

## Follow-on (filed, not done)

- **Session task #11** — a migration rule to rewrite tuple **types** in signatures from parenthesized `(A, B)` to `%[A, B]` (the unified-tuple surface), requested mid-run. Investigation attached to the task: neither branch's stdlib carries the syntax in type position, so the change lives in the parser's tuple-type grammar; the executor should start from the parser diff (main vs `feature/idris-parity`) and derive the rewrite from real AST node shapes. Sequenced after this editions work so it inherits the tier/provenance machinery. **Not part of this branch.**

## Next step for the operator

Review and merge `autopilot/editions` into `feature/idris-parity`. The worktree is preserved.
