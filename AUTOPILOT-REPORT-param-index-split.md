# Autopilot completion report — parameter/index split

**Branch:** `autopilot/case-index-unification` (worktree; **not merged** — review + merge is yours)
**Result:** full suite **2158 passed, 0 failures** (baseline 2137 + 21 new tests).

## What shipped

Cure now has a **true parameter/index split** for indexed families. A head-paren
argument is a *parameter* (uniform across all constructors, never matched, bound
outside each constructor's telescope); the `indices (…)` clause lists the
refined indices. Non-uniform parameters are rejected (Agda model). Surface:

```
type Vector(a: Type) indices (n: Nat)     # a = parameter, n = index
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

The legacy `indexed type NAME(...) where` syntax is **retired** (parser arm
removed); all stdlib/examples/fixtures/tests migrated.

## Stage log

| Stage | Outcome |
|-------|---------|
| 0 Brainstorm | Design approved interactively; spec written + hardened (`7b9dfb1`). Decisions: `type N(params) indices (idx)` surface, constructors restate the parameter, reject non-uniform parameters, Idris-style inference deferred. |
| 1 Spec review | Sonnet recursive-skeptical-review → hardened spec committed. |
| 2 Plan | 8-task TDD plan (`3647bb6`). |
| 3 Plan review | Sonnet review found the parameter-seeding gap; plan hardened (`529fb56`). |
| 4 Execute (Opus, TDD) | 8 tasks, per-task commits (below). |
| 5 Verify | Full suite once: **2158 passed, 0 failures**. |

## Commits (Stage 4)

- `126074d` core: record datatype parameters separately from indices (Inductive `ctor/5`, `param_count`, `result_params`)
- `9808b5f` kernel: reject non-uniform parameters in `check_ctor`
- `d11b71a` kernel: resolve constructor parameters via checking mode; `vdata` carries `params ++ indices`
- `db1f111` kernel: `case` splits params from indices; motive over indices only
- `25e3000` parser: `type NAME(params) indices (idx)` syntax
- `da1a479` elab: split parameters from indices in indexed-type declarations
- `9410d1c` elab: thread datatype parameters through match + ctor-app elaboration
- `8e39ae6` std: migrate to new syntax; retire legacy; end-to-end integration fixes

## Deviations from the plan (worth a look during review)

1. **Legacy-syntax blast radius (Task 8).** The plan listed only 3 `.cure` files
   to migrate; in fact ~20 inline test declarations used the old syntax. Retiring
   the legacy parser arm (as the plan mandates) required migrating all of them.
   The `SF` families are parameter-free, so those migrations are semantics-
   preserving; `vec_dependent_test`'s Vector assertion was updated from
   `indices: [a, n]` to `params: [a], indices: [n]` to encode the corrected
   design (the one assertion that named the old split).

2. **Untrusted-elaborator integration fixes (Task 8, beyond plan Task 7).** The
   plan assumed `Std.Vector.append` would type-check unchanged after migration.
   It did not — three parameter-awareness gaps in the *untrusted* elaborator,
   not covered by the plan, surfaced and were fixed with the same param-seeding
   discipline the plan's review applied to the trusted kernel:
   - `idx_to_core` now splits a surface `{:data,…}` by `param_count` (else
     `infer({:data})` fails `:arg_arity`); the family is pre-registered so
     self-references in constructor signatures resolve their parameter arity.
   - `elaborate_ctor_app` seeds parameters as leading erased metavar slots
     (solved by unifying present args); `finish_ctor_app` splits them out.
   - `extend_context` seeds a match branch's constructor telescope with the
     scrutinee's actual parameter values, so a constructor arg typed at the
     parameter (`append`'s `rest`) is usable in the branch body.

   These are covered by a new focused regression test plus the pre-existing
   `vec_dependent_test` append test and `slice1` conformance.

## Not done (intentionally deferred)

- Optional Idris-style **parameter inference** (spec §9) — additive, future.
- Sub-projects ② (Eq/rewrite consolidation) and ③ (Antigen rewrite/Eq vertical).
- case-index-unification's own Task 2 (impossible-branch discharge).
