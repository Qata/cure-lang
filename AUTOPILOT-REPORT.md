# Autopilot completion report — antigen-pre-port-banking

**Status: COMPLETE.** Branch `autopilot/antigen-pre-port-banking` (worktree
`.claude/worktrees/antigen-pre-port-banking`), cut from `ed0779c` (HEAD of
`autopilot/case-index-unification`, per operator instruction). 15 commits,
final suite **2215 passed, 0 failures**, clean tree. **Not merged** — review
and merge when ready. Note: this branch builds on the (unmerged)
case-index-unification branch; merging this one brings that history with it.

## Stage outcomes

| Stage | Outcome | Commits |
|---|---|---|
| 0 Spec | pre-existed on base branch (brainstormed in a prior session) | f7ef85a, bcbcdce (inherited) |
| 1 Spec review (Sonnet) | 9 passes, 4 fixes (gate-5 completeness, D4 symmetric reroute, D2 shape-drift clarification, gate-4 W3 extension) | 507f894 |
| 2 Plan reconcile | plan pre-existed; folded hardened-spec changes in (reroute contingencies, #13 correction, hedged ledger closes) | 32bced5 |
| 3 Plan review (Sonnet) | 5 passes, 6 fixes (reach-test generalization guidance, test-immutability rule, spec-divergence note, symmetric soundness contingency, conditional file tracking, count fix) | d8d865a |
| 4 Execute (Opus subagents, TDD) | Tasks 1–11 all complete | e05950d … c927e5b |
| 5 Verify | full suite once: 2215/0; five banking/pin tests byte-stable; authors verified (all ghost-written, no trailers) | — |

## Headline findings (three kernel-level discoveries, two fixed red-green)

1. **Crash-class TCB gap (W3 audit):** `Cure.Core.Term.shift/3`, `subst/3`,
   and `term?/1` had no clauses for literal/type-constant Core terms
   (`{:int_lit,_}`, `{:int_type}`, bool/float forms). The first literal type
   index to reach the case-index unifier crashed `unify_indices` with a
   `FunctionClauseError` before the deletion rule was ever consulted.
   Fixed + regression-tested in `360402b` (TCB commit,
   `test/cure/core/term_literals_test.exs`).
2. **Two live positivity soundness holes (W4 audit, exactly as the plan
   predicted):** the sigma-hidden negative occurrence and the
   through-constructor escape (`Bad ≅ (Bad -> Dec)` via `Box`) were both
   wrongly ACCEPTED by the shallow positivity walk; double-negation was
   already rejected. Fixed by the deep strict-positivity walk (env-aware
   constructor expansion + Σ traversal) in `6148aff` (TCB commit); the three
   W4 challenges are its permanent regression guards.
3. **Universes fully sound (W5 audit):** all six probes green on first run —
   no Type-in-Type, ceiling enforced, cumulativity + stratification accepted,
   two-universe ctor-field rule enforced both ways. Roadmap #20's claims
   verified; the subsystem had zero Antigen coverage before this run.

No D4 incompleteness reroute fired anywhere; `reach.sexp` holds only the
three intended W2 pins.

## What was banked

- `corpus.sexp` 5 → **17** (+5 W1 adversarial diverging antibodies [LJB
  discriminators], +1 W3 deletion-rule antibody, +3 W4 positivity escapes,
  +3 W5 universes antibodies)
- `seeds.sexp` 22 → **25** (+1 W3 deletion well-typed, +2 W5 well-typed;
  `stratification`/`ctor_field(:well_typed)` are coverage-equivalent under
  the plateauing seed key, so only one banks — apparatus design, the other
  stays guarded by the per-run assay test)
- `reach.sexp` (new store) — **3** W2 reach pins (even/odd, Ackermann,
  permuted pair), each pinned to its documented conservative rejection;
  P1 migrates them per D2
- Kernel-level occurs-check pin: `test/cure/core/branch_unify_occurs_test.exs`
  (documented divergence from spec W3's literal framing — see plan Task 6)
- Roadmap ledger closed: A1 (stale-closed, + #13), A2/#23, A3/#19, A4, A9

## Per-task commits (Stage 4)

- Task 1 (W6 hygiene): `e05950d`
- Task 2/3 (W1 + bank): `cf69a92`, `579d3fe`
- Task 4/5 (W2 + reach store): `f5dda56`, `abca92e`
- Task 6 (W3, incl. TCB fix): `360402b`, `051f20b`
- Task 7/8 (W4 audit + deep positivity fix): `6148aff`
- Task 9 (bank W4): `51e5f39`
- Task 10 (W5 universes): `74277f7` (plan amendment), `612ed01`
- Task 11 (ledger + final gate): `c927e5b`

## Deviations from the plan, all documented in-line

1. Task 6: kernel `Term` crash was not one of the plan's two anticipated
   contingency verdicts → coordinator-approved red-green TCB fix (spec §7 /
   gate 4 permits kernel changes forced by a W3 audit surprise).
2. Task 10: seed-count literal `>= 6` → `>= 5` under the plan's
   test-immutability carve-out (wrong prediction about intended
   coverage-plateau dedup semantics: one seed per coverage cell), plan
   amended first in `74277f7`.
