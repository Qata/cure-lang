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

## Full-suite verification (run once)

`mix test` → **4262/4264 passed, 1 skipped, 2 failures**. Both failures are
pre-existing and unrelated to this run's diff:

1. **`Cure.Migrate.MonotonePropertyTest` — non-monotone on `lib/std/actor.cure`.**
   Classified empirically: reverting `lib/std/actor.cure` to baseline
   `53b63996` and re-running the monotone test **still fails identically**. The
   migration Printer does not round-trip the pre-existing `quote`/`$()` sites in
   `actor.cure` to a fixpoint (the `90612376` printer fix stopped it *raising*
   but did not make the round-trip idempotent). Standing migration-facility gap,
   not caused by Task 1/2/3. The additive parser clause is inert on baseline
   `actor.cure`, which has no `Declarations` family field.

2. **`Cure.Elab.UnionTest` — `:"Cure.Std.Map".get/2 is undefined or private`.**
   The diff touches nothing near `Std.Map` or union elaboration. Pre-existing.

Neither is a regression introduced by this run.

## Deferred (NOT in this run — future stages)

- **1c** — whole-module `quote` (module-level template).
- **1e** — terse Tier-1 shorthand delegating to the expander, deletion of the
  legacy Gen A positional `becomes` template rules, and demo migration.
- **Stage 2** — apply the same consolidation to `fsm` / `supervisor` /
  `application` macros.
- **Stage 3** — typed Tier-3 elaborator (Lean-style MetaM direction).

## Follow-up worth filing (independent of this branch)

The migration facility's monotone law is red for `actor.cure` because `quote`/
`$()` nodes don't reprint to a fixpoint. Worth a dedicated red-test-first fix in
`Cure.Compiler.Printer` / `Trivia` — out of scope for the actor consolidation.

## Next action for the operator

Review and merge `autopilot/actor-macro-consolidation`. The two full-suite
failures are pre-existing on the baseline and are **not** expected to be green.
