# Autopilot completion report — sub-project ② (case-refinement no-confusion + impossible-branch discharge)

**Branch:** `autopilot/case-index-unification` (worktree; **not merged** — review + merge is yours)
**Result:** full suite **2169 passed, 0 failures** (baseline 2165 + 4 new tests).

## What this was — and the pivot

Sub-project ② was framed as "build a pattern-fragment unifier for case-refinement
(injectivity + no-confusion + occurs-check)". Grounding in the *current* kernel
revealed it was already **Task 2 of an existing, hardened, Sonnet-reviewed plan**
(`docs/superpowers/{specs,plans}/2026-07-01-case-index-unification-*`): **Task 1
had already shipped** (`5646c63`), giving the kernel the *solution*, *deletion*,
*injectivity* (`unify_spine` over matching constructor heads), and *occurs-check*
rules. So autopilot Stages 0–3 were already satisfied by committed reviewed
artifacts; this run executed **Stage 4 (Task 2) + Stage 5** only.

**Scope confirmed by user:** *kernel-only*. Surface alignment (dependent
index-varying motives, absurd patterns, aligning with Idris' `Core/Unify.idr`)
is deferred as **sub-project ④**.

## What shipped (Task 2)

The two Agda/Idris unification rules that complete no-confusion:

- **Conflict / no-confusion** — a definite rigid constructor/data head clash in
  `unify_indices` now returns `:impossible` (was conservatively `:undecided`).
  Two sites: `unify_one`'s clash fallthrough, and `bind_index`'s same-key merge
  conflict (two unequal rigid bindings for one telescope var).
- **Impossible-branch discharge** — `check_case_branches` gained a real
  `:impossible` arm that discharges an unreachable branch **without checking its
  body**. A *reachable* branch with the same body is still rejected — discharge
  is not a blanket bypass. (Preserved the post-① 3-arg
  `extend_with_telescope(ctx, tele, scrut_params)`, computed only in the
  non-impossible arm.)

Soundness boundary held exactly (spec §5): `:impossible` fires **only** on a
definite rigid head clash or same-key conflict; uncertainty stays `:undecided`;
occurs-check on every bind.

### The kernel now has the full Agda/Idris case-refinement rule set

| Rule | Status |
|------|--------|
| Solution (`x := t`) | ✓ Task 1 |
| Deletion (`t = t`) | ✓ Task 1 |
| Injectivity (`C u⃗ = C v⃗ ⟹ u⃗ = v⃗`) | ✓ Task 1 (`unify_spine`) |
| Conflict / no-confusion (`C ≠ D ⟹ absurd`) | ✓ **Task 2** |
| Impossible-branch discharge | ✓ **Task 2** |
| Cycle / occurs-check | ✓ Task 1 (sound degrade to `:undecided`) |

## Tests (all in `test/cure/core/case_soundness_index_test.exs`)

- **Test 3** — impossible `wrap` branch (scrutinee `Ix Dcoupled`, `wrap` builds
  `Ix Causal`) discharged though its body is ill-typed `{:type,0}`.
- **Test 3 companion** — same ill-typed body in a *reachable* (`Ix Causal`)
  branch is still rejected.
- **Test 5a** — direct positional clash in a multi-index family `Foo` (no shared
  key; `unify_one`'s own catch-all fires).
- **Test 6** — same-key merge conflict (`mk:(p)->Foo(p,p)` vs `Foo(Causal,Dcoupled)`)
  yields `:impossible`, not a silent overwrite.

RED→GREEN confirmed: pre-fix 6/9 (Tests 3/5a/6 failed), post-fix 9/9.

## Commit

- `f16d008` feat(kernel): discharge impossible case branches; merge-conflict is impossible

## Stage log

| Stage | Outcome |
|-------|---------|
| 0–3 | Pre-satisfied by committed, Sonnet-reviewed spec + plan (`b7e2e2d`, `ab3d1fa`); Task 1 already shipped (`5646c63`). |
| 4 Execute (Opus, TDD) | Task 2: red (6/9) → green (9/9), one commit. |
| 5 Verify | Full suite once: **2169 passed, 0 failures**. |

## Net / guard

③'s `rewrite/eq` vertical and the indexed-case Antigen vertical both stayed green
through this kernel change — the propositional escape hatch and the refinement
obligations are intact.

## Not done (intentionally deferred)

- **Sub-project ④ — surface alignment.** Study Idris' `Core/Unify.idr`; thread
  dependent (index-varying) match motives and absurd (`impossible`/`()`) patterns
  through the untrusted elaborator + parser so `.cure` source can drive
  impossible-branch elimination end-to-end. Its own autopilot run.
- Optionally, a dedicated no-confusion/injectivity **Antigen vertical** as a
  standing net for this kernel rule set (candidate future deep cut).
