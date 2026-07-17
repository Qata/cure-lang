# Autopilot completion report — actor-macro consolidation (Stage 1: actor)

**Branch:** `autopilot/actor-macro-consolidation` (cut from HEAD; **NOT auto-merged**)
**Run date:** 2026-07-16
**Outcome:** ✅ Complete. All planned Stage-1 (actor) tasks landed green; both
full-suite failures classified as **pre-existing and unrelated** to this run.

> Replaces the earlier `editions`-run report carried in via the HEAD cut (that
> report remains in git history).

## What this run delivered

Consolidated `lib/std/actor.cure`'s expansion path toward ONE quote-templated
backend (`derive_actor_family` → `emit_actor_parts` / `emit_actor_call_parts`),
per the approved Lean-style 3-tier macro design. **Stage 1 (actor) scope only.**

| Task | Deliverable | Commit |
|------|-------------|--------|
| 1 (1a) | Fold `derive_actor` into `derive_actor_family` (single entry) | `fa270d5a` |
| 2 (1b) | Templatize the 4 fixed-param callbacks with `quote` | `7511959e` |
| 3 (1d) | `body Declarations` passthrough into the generated module | `a8fe90fe` |

Task 3 required a P-layer parser addition — a `parse_family_field_value` clause
for `%{shape: "Declarations"}` using `parse_definition_block`, so a `body` block
captures *declarations* rather than expressions. Spec §9 permits P-layer
changes; **TCB (`lib/cure/core/*`) untouched.**

## Stage-by-stage trail

| Stage | Action | Commit |
|-------|--------|--------|
| 0 | Spec written | `ad343b07` |
| 1 | Spec hardened (recursive-skeptical-review, Sonnet) | `441cbd80` |
| 2 | Plan written | `f6ddf778` |
| 3 | Plan hardened (recursive-skeptical-review, Sonnet) | `53b63996` |
| 4 | Execute (inline TDD, Opus) | `fa270d5a`, `7511959e`, `a8fe90fe` |
| 5 | Code review (recursive-skeptical-review, Sonnet) | zero confirmed findings — no fix commit |

Diff scope (code): `lib/cure/compiler/parser.ex` (+7), `lib/std/actor.cure`
(refactor, net −20), `test/cure/compiler/actor_computed_test.exs` (+21, one new
immutable behavioral test — "structured actor threads a body declaration into
the generated module"). 3 files.

## Full-suite verification

**Final state (after merging `feature/idris-parity`, merge commit `78c3455a`):**
`mix test` → **4306 passed, 1 skipped, 0 failures** (Antigen shape-coverage
318/318; 156 expected immune responses). Fully green.

At the end of the autopilot run itself (before the merge) the suite showed
**4262/4264 passed, 1 skipped, 2 failures**, both classified pre-existing and
unrelated to this run's diff — and **both were subsequently resolved by the
`feature/idris-parity` merge**, confirming neither was a regression from this
run:

1. **`Cure.Migrate.MonotonePropertyTest` — non-monotone on `lib/std/actor.cure`.**
   Classified empirically: reverting `lib/std/actor.cure` to baseline
   `53b63996` and re-running the monotone test **still failed identically**, so
   the pre-existing `quote`/`$()` sites — not Task 1/2/3 — were the cause. The
   `feature/idris-parity` printer fixes (+74 lines in
   `lib/cure/compiler/printer.ex`) make the round-trip idempotent; the test now
   passes.

2. **`Cure.Elab.UnionTest` — `:"Cure.Std.Map".get/2 is undefined or private`.**
   The diff touched nothing near `Std.Map`/union elaboration; resolved by the
   idris-parity work brought in by the merge.

## Deferred (NOT in this run — future stages)

- **1c** — whole-module `quote` (module-level template).
- **1e** — terse Tier-1 shorthand delegating to the expander, deletion of the
  legacy Gen A positional `becomes` template rules, and demo migration.
- **Stage 2** — apply the same consolidation to `fsm` / `supervisor` /
  `application` macros.
- **Stage 3** — typed Tier-3 elaborator (Lean-style MetaM direction).

## Post-run merge

`feature/idris-parity` was merged into this branch (`78c3455a`, ghost-authored,
no conflicts) to pick up its `printer.ex` fixes. The merge left `actor.cure`
untouched, so the Stage-1 actor work is intact, and it brought the tree to
**0 failures** (see Full-suite verification above).

## Next action for the operator

Review and merge `autopilot/actor-macro-consolidation`. The tree is fully green
(0 failures) after the `feature/idris-parity` merge.
