# Autopilot completion report — axiom-free refinement reflection

Branch: `autopilot/axiom-free-refinement-reflection` (worktree). **Not merged** — awaiting operator review/merge.

(Note: the pre-existing `AUTOPILOT-REPORT.md` in this tree is a stale report
from an unrelated earlier run — type-directed overload resolution — carried in
on the HEAD cut. It was left untouched.)

## What shipped

An **axiom-free** bridge connecting Cure's primitive-`Int` refinement world
(`IsTrue(bool comparison)`) to the inductive `Nat` proof families
(`IsPositive` / `IsLessThan` / `IsLessThanOrEqual`), so open refinement
obligations discharge from the `Std.Proof.Math` lemma library **without a
solver and without new kernel trust**. No axioms, no `@extern`, no
`believe_me`, no `lib/cure/core/*` (TCB) edit.

Three layers plus two coercions:
- **Layer 1** — `Std.Proof.BooleanReflection`: boolean-connective algebra over
  `IsTrue` (conjunction split/build, disjunction intro, negation contradiction).
- **Layer 2** — `Std.Proof.Math` Nat reflection: boolean comparisons
  (`natural_is_less_than` etc.) reflected to/from the inductive relations.
- **Layer 3** — runtime `decide_is_true` at boundaries (worked example, no new
  machinery).
- **Projections in proof search** — a syntax-directed *conjunction-elimination*
  candidate source (`IsTrue(and(l,r))` hypothesis discharges `IsTrue(l)`/
  `IsTrue(r)` goals) and a *refinement→base* coercion (`sigma_first`), both
  kernel-rechecked in the untrusted elaborator.
- `to_integer : Nat -> Int` total projection.

## Stage outcomes

| Stage | Outcome |
|-------|---------|
| 0 Brainstorm | design approved; spec written + committed (`2f459d7a`) |
| 1 Spec review | hardened (`05af5ae3`) |
| 2 Plan | committed (`57600b0f`) |
| 3 Plan review | hardened (`be250ec7`) |
| 4 Execute (Opus, TDD) | 8 tasks, per-task commits `2e1a5b0c..9d6044dd` |
| 5 Code review (Sonnet) | **converged clean — zero confirmed findings, no fixes needed** |
| 6 Verify + report | this document |

## Implementation commits (Stage 4)

- `2e1a5b0c` feat(std): boolean-connective algebra over IsTrue
- `337ab4ec` feat(std): boolean-valued Nat comparisons
- `f537ba05` feat(std): Nat reflection lemmas bridging boolean and inductive comparison
- `f6d6dbed` feat(std): total Nat to Int projection
- `5f55d7e5` feat(elab): coerce refinement value to its base type via sigma_first
- `f78fdf9f` feat(elab): conjunction-elimination candidate source in proof search
- `4b8f2eab` test(oracle): boolean-connective and Nat-reflection differential probes
- `9d6044dd` test(std): worked decide-at-boundary example (Layer 3)

## Final gate (run once, serially)

- **Full suite** (`mix test --include slow`): **4806 passed, 1 skipped**
  (3 doctests); Antigen shape-coverage **318/318 cells** across 31 assays.
- **Antigen** (`mix antigen`): exit 0, all three health checks **healthy**,
  mutant **survivors = 0**, 143 immune responses (expected).
- **Oracle replay** (`test/oracle_replay_test.exs`): **81 passed** — includes
  the three new probes `refine03`/`refine04`/`refine05`, all `rel=same`, both
  Cure and Idris `accept`.

## Follow-up: OPEN-refinement discharge wired into proof search (`0d1e2f17`)

After the report above, one gap remained: closed refinement obligations
discharged via `reflection_proof` (nullary `Confirmed()`), but **open**
obligations — whose truth depends on a free binder — were not routed to the
auto-lemma proof search. Commit `0d1e2f17` closes that:

- `try_discharge_refinement/5` now falls through to `discharge_obligation/3`,
  which tries `reflection_proof` first, then `ProofSearch.resolve/3` for the
  open case. Every candidate stays kernel-rechecked — no new trust.
- A **tuple-exclusion guard** (`tuple_telescope_type?/4`, a transitive-closure
  Unit-terminator probe) keeps unified-tuple `Sigma` telescopes from being
  mistaken for genuine refinements, so Optic/actor code is untouched.
- `elaborate_body`'s refinement-return routing is **infer-first**: a body that
  already infers to a refinement value (`refine(v, pf)`) is kept verbatim; only
  a base-valued body is re-checked against the refinement goal for discharge.
  This fixed a differential-golden regression where a hand-written reference's
  implicit value-args had begun elaborating to `sigma_first` instead of
  `refined_value`. The discriminator uses value-safe `whnf_value` inspection
  (`inferred_refinement_value?/3`), never `Kernel.normalize` on a semantic value.
- `and`/`or` binop globals now qualify to `Std.Bool#and` / `Std.Bool#or`.
- `Std.Proof.Math.successor_is_positive` carries the `@lemma` tag so the
  positivity family is reachable by search.
- Test sweep: `refinement_usecase_matrix_test.exs` (5 use-case tests) and
  `refinement_proofsearch_discharge_test.exs` (2 tests).

Elaborator-only (E-layer); no `lib/cure/core/*` (TCB) edit.

### Refreshed final gate (run once, serially, after `0d1e2f17`)

- **Full suite** (`mix test --include slow`): **4813 passed, 1 skipped, 0
  failures**.
- **Antigen** (`mix antigen`): shape-coverage **318/318 cells**, 138 immune
  responses (expected), mutant survivors = 0.
- **Oracle replay** (`test/oracle_replay_test.exs`): **81 passed**.

## Notes

- refine03/04 pin both connective operands explicitly on *both* sides (Cure
  lemma args explicit; Idris `soAnd`/`orSo` implicits named `{a=…}{b=…}`), so
  neither side depends on post-reduction operand inference. refine05 mirrors
  Cure's boolean→inductive reflection with Idris `ltOpReflectsLT`.
- QTT-honest: every lemma that inducts on an operand takes it explicit
  (grade-ω); a grade-0 erased operand genuinely cannot be discharged, and the
  discharge tests supply relevant/concrete operands accordingly.
