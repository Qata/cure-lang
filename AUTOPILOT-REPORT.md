# Autopilot completion report — Type-directed overload resolution (Ph1)

**Branch:** `autopilot/type-directed-overload-resolution` (cut from HEAD at the spec commit)
**Status:** ✅ Complete — ready for operator review & merge. NOT auto-merged.
**Final HEAD:** `a10f8b08`
**Full suite:** 4742 passed (3 doctests, 4739 tests), 1 skipped, 2 excluded, Antigen 318/318 ✓
**TCB (`lib/cure/core/**`):** untouched — zero-TCB constraint held throughout.

> Replaces an earlier unrelated run's report (`actor-macro-consolidation`) carried
> in via the HEAD cut; that report remains in git history.

## What shipped

Ph1 **named** type-directed overload resolution for Cure (Idris2 elaborate-and-prune),
keyed by `(name, arity, argument types)`. Several functions may share a bare name;
the applied call site gathers the candidate set and prunes by inferred argument type.
Exactly one survivor resolves; none → `{:no_matching_overload}`; more than one →
`{:ambiguous_overload}`. Works for same-module AND cross-module (`use`d) overload sets
(Design "Both"), with the dot-qualified spelling as the escape hatch. This retires the
stdlib rename workarounds (`Std.Measurements.add`/`sub`, `Std.Char.code_point`).

**Explicitly out of scope (deferred):** operator conformance (making `+` "just work"
on a user type) and Swift-style argument labels — both await the precedence-group spec.

## Stage-by-stage outcome

| Stage | Outcome | Commits |
|---|---|---|
| 0 — Brainstorm + spec | Design "Both" approved (single human gate); spec written & committed | `56765820` |
| 1 — Spec review (Sonnet) | recursive-skeptical-review → hardened spec | `cf4db2d4` |
| 2 — Plan (inline) | Implementation plan written | `0ab765b2` |
| 3 — Plan review (Sonnet) | recursive-skeptical-review → hardened plan | `2a9a8829` |
| 4 — Execute (Opus, TDD) | 8 per-task commits; red-green throughout | `e417d5b6` `edb83833` `59d54e2d` `71e4f57f` `5b2cc68b` `70a3c676` `8c373019` `6e8f827c` |
| 5 — Code review (Sonnet) | recursive-skeptical-review, 2 consecutive clean passes; 1 finding fixed | `a10f8b08` |
| 6 — Verify + report + notify | Full suite green; this report; push notification | — |

## Key implementation notes

- **Discriminator:** overload members register under a `~<ordinal>` suffix
  (`Mod#plus~0`, `Mod#plus~1`). **Size-1 sets stay byte-identical** (`Mod#plus`) —
  inertness is pinned by test (`OvlInert`) and verified in Stage 5.
- **Pruner soundness (`overload.ex`):** prunes on **present (non-erased)** parameter
  domains only, so a polymorphic member like `Std.List#length : {t} -> List(t) -> Nat`
  is matched on its present `List(t)` (arity 1) rather than dropped by counting the
  erased `{t}`. A present param still mentioning a telescope binder is **conservatively
  kept** — the pruner errs toward ambiguity, never toward a silent wrong unique pick.
- **Diagnostic taxonomy:** an *applied* bare doubly-imported call → `{:ambiguous_overload,
  name, owners}`; an *un-applied* value reference (no args to prune) stays the
  pre-resolution `{:ambiguous_name}`. `global_namespace_soundness_test.exs:170` was
  migrated to the applied-path tag faithfully (the soundness property — no
  last-merge-wins — is preserved).

## Stage 5 finding (fixed)

The only finding was a **coverage gap**: `Resolution.overload_candidates/2` relies on
`prefer_local` running before `prefer_direct` (a module's own overload members are never
in its own `import_modules`; the reverse order would let an ambient `@prelude` provider
like `Std.Nat#plus` masquerade as the sole candidate). The shipped code was correct but
untested. The reviewer proved it by swapping the filters — which broke the stdlib's own
build (`Std.Vector`/`Std.Optic`'s locally-overloaded `map`) — then added a permanent
regression test. **No production code changed** (`a10f8b08`, test-only).

## Deferred: differential-oracle probe

The plan's optional oracle probe (mirroring resolution against `idris2 --check`) was
**not** built: Idris's overloading mechanism differs enough that no cheap faithful mirror
exists, and the internal suite already covers the resolution/ambiguity/inertness surface.
Left as a future item, not a gap in this feature.

## Next action for the operator

Merge `autopilot/type-directed-overload-resolution` into `feature/idris-parity` when
ready. No further sub-projects were decomposed from this idea.
