# Autopilot completion report — migration facility

**Branch:** `autopilot/migration-facility`
**Status:** ✅ complete — full suite green (3438 passed, 0 failures), **not merged** (operator merges).
**Date:** 2026-07-10

## What was built

A general **source-migration facility** for Cure plus a `cure migrate` command:

- New editions accept old syntax via an auto-translation pipeline that emits
  deprecation warnings during `cure build` (warn-and-tolerate), while
  `cure migrate` applies the rewrites and reprints the file canonically.
- `cure migrate` **refuses to run** unless every target file is git-tracked and
  the tree is porcelain-clean, so every migration is reviewable/revertible as a
  diff. `--check` (CI, writes nothing), `--print` (stdout, git-guard-exempt),
  and `--strict` (warnings→error) modes.
- Whole-file **canonical reprint** (Approach A) built on a total trivia model
  (comments + blank lines attached to node meta) and a total Printer that
  applies the fully-opinionated §5.4 blank-line policy (blank line between every
  top-level def, none at file top, one at file bottom).
- A **rule registry** (`Cure.Migrate`) with an ordered-fold `run/2` engine and
  three day-one seed rules.

## Stage-by-stage outcome

| Stage | Outcome | Key commits |
|-------|---------|-------------|
| 0 — Brainstorm | Design approved by operator; spec written + committed | `e6287f1` |
| 1 — Spec review (Sonnet) | Hardened to convergence | `bcea259` |
| 2 — Plan | Implementation plan written | `d0cd1a8` |
| 3 — Plan review (Sonnet) | Hit 15-pass ceiling → halted; operator added `@group` seed rule; resumed | `0126aa9`, `c97972e`, `981b5ed`, `a7aabe8`, `53ba0b8` |
| 4 — Execute (Opus, TDD) | 13 tasks, one build/test at a time, commit per task | see below |

### Stage 4 per-task commits

- `0440071` Printer raises on unprintable nodes (was silent `inspect`)
- `0f40242` Printer totality/corpus/exhaustiveness gates (red)
- `0afd1d8` Printer total + byte-fixpoint over the corpus
- `f8b5ea9` Lexer collects positioned comment/blank trivia
- `216e939` Total post-parse trivia attachment pass
- `3449dad` Printer emits attached trivia (lossless round-trip)
- `e0f73ba` §5.4 blank-line policy
- `18cf6b9` Rule registry + ordered-fold `run/2`
- `da1b730` if/elif→pickup rule (reparse-equivalence guard, comment carry)
- `7eb7990` uppercase-type-var→lowercase rule (ctx resolution + freshening)
- `19a9e37` @group hoist relocation rule (trivia carry)
- `ce17a71` `cure build` warn-and-tolerate consumer + parity guard
- `acc9a2d` git-safety preflight guard (tracked + porcelain-clean)
- `3bbdb9e` `cure migrate` CLI (check/print/strict, batch atomicity)
- `92d639e` route `mix cure.rewrite` through the shared registry

## Design decisions worth flagging on review

1. **`tolerate_safe?` per-rule flag + `:apply` mode** (deviation from the spec's
   flat "normalize in-memory"). Compiling the *rewritten* AST during `cure build`
   regressed `vector.cure` with `{:unsolved_metavariables}` — lowercasing
   dependently-typed type vars is not safe to fold silently into compilation. Per
   the spec's own "normalize in-memory **where safe**" qualifier, `cure build`
   now runs in `:safe_only` mode: it *warns* for every fired rule but only folds
   the rewrites of rules flagged `tolerate_safe?` (all three seed rules default
   `false`), so the compiled AST stays the original. `cure migrate` uses `:all`.

2. **Verify-by-reparse-equivalence** for if/elif→pickup: the rule reprints the
   candidate, reparses it, and requires *structural* equality — not mere reparse
   success — before accepting a rewrite. This is what makes a conditional
   embedded in a call-argument list (which Cure's layout-sensitive parser cannot
   represent as a multi-line pickup block) correctly left untouched.

## Follow-up (not in scope of this run)

- The stdlib emits **many** `uppercase type variable will be lowercased`
  warnings (see `vector.cure` etc.). Running `cure migrate lib/std/**/*.cure`
  would clear them — but that rewrite is `:needs_resolution` and touches
  dependently-typed signatures, so it wants a human-reviewed diff, which is
  exactly what the git-guarded `cure migrate` produces. Recommended as a
  separate, reviewed pass.

## Merge

Review and merge `autopilot/migration-facility` into `feature/idris-parity`
when ready. Nothing was auto-merged.
