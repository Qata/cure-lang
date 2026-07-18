# Autopilot Completion — Auto-Lemma Proof Search

**Branch:** `implicit-goal-solving` (worktree; **NOT auto-merged** — left for operator review)
**Feature:** `Cure.Elab.ProofSearch` — goals like `IsPositive(multiply(a,b))` discharge
automatically from `@lemma`-tagged theorems + local hypotheses + refinement/Sigma
projections, without the author naming the lemma.

## Stage outcomes

| Stage | Outcome |
|-------|---------|
| 0 — Brainstorm + spec | Design approved; spec written + hardened (`93ca131f`, `f0f20374`) |
| 1 — Spec review (Sonnet) | Converged; committed |
| 2 — Plan | `4fa16a9e` |
| 3 — Plan review (Sonnet) | Converged (`1753705b`) |
| 4 — Execute (Opus, TDD) | Tasks 1–9 green, per-task commits `b6ff84cf … 1bd00108` |
| 5 — Code review (Sonnet) | 6 passes (last 4 clean); 2 defects fixed red-first + 1 self-regression caught |
| 6 — Full gate | **Green** (see below) |

## Full gate (run once, alone)

- `mix test --include slow`: **4749 passed, 1 skipped**; Antigen shape-coverage **318/318** cells.
- `mix antigen` (generative metatheory): **exit 0**, all three subsystems `healthy`, `survivors=0`
  (336 immune responses triggered — all deliberately-injected mutants caught).
- Coverage-floor tripwire re-recorded (`cff0f2da`): the TCB structural walkers
  (`Eval`/`Conv`/`Quote`) gained a `{:nhole,_}` clause each; covered floors unchanged
  (nothing regressed), only totals grew.

## What shipped

- **First-class holes (TCB):** `{:hole,id}` → `{:nhole,id}` stuck neutral in `Eval`, with
  congruence in `Conv` and reification in `Quote`. A declined proof hole *survives* (blocks
  codegen via `check_codegen_ready`) instead of crashing the evaluator.
- **`@lemma` registry:** inert lemma table on `Core.Env`, registered by conclusion head,
  merged (and now **deduped**) across `use`-imports.
- **Resolver (`proof_search.ex`, untrusted):** local-context + refinement-projection +
  lemma-application candidates; whnf goal head exposure; depth+cycle termination; every
  assembled term re-checked by `Kernel.check` before acceptance. `decide/2` collapses
  identical-term candidates so a **diamond import** is not a false ambiguity, and surfaces
  genuinely-distinct survivors as `:ambiguous_proof_search`.
- **Shipped stdlib demo:** `Std.Refine.multiply_positive_natural_numbers` leaves its proof a
  `?` hole, discharged cross-module from `Std.Proof.Math`'s `@lemma`-tagged
  `multiplying_positive_numbers_is_positive`.

## Continuation-session fixes (this run)

1. **Diamond-import false ambiguity** — tagging the stdlib lemma made `IsPositive(multiply)`
   ambiently provable, so the same lemma reaching a goal via two `use` paths produced two
   identical candidates → spurious ambiguity. Fixed by term-dedup in `decide/2` +
   `Enum.uniq` in `merge_env/2` (`1bd00108`).
2. **Proof-hole fixtures re-based** — Task 8's `proof_hole_resolution_test` fixtures targeted
   `IsPositive(multiply)`, which the newly-tagged stdlib lemma both discharges (killing the
   `@red` decline case) and duplicates (making `@green` ambiguous). Re-based onto a local
   `IsFoo` proposition no stdlib lemma proves, isolating tag-gating while still driving the
   cross-module refinement-projection path (`1bd00108`).
3. **Stage-5 review fixes** — (a) ambiguous lemma *sub-goals* were swallowed as `:none`
   (`2ab97b78`); (b) a vacuous cross-module merge test replaced with a real disk-loaded
   two-module one (`153f875d`); (c) a self-introduced regression (ordinary unify failure
   conflated with ambiguity) caught and narrowed to the `{:ambiguous_proof_search,_,_}`
   shape (`420451a1`).

## TCB note

The holes feature touches `lib/cure/core/*` (Eval/Conv/Quote) — a TCB change. It is covered
by red-green unit tests, a dedicated Antigen antibody (`hole_neutral_antibody_test.exs`), the
full Antigen generative suite (green), and the coverage-floor gate. Per the standing TCB
blanket approval, first-class holes align with holes/metavariables as stuck neutrals in
Idris/Agda/Lean. **Operator review of the TCB diff is still warranted before merge.**

## Open follow-ups (non-blocking)

- The new `{:nhole,_}` clauses in `Eval`/`Conv`/`Quote` are exercised by unit + antibody
  tests but not by the Antigen *coverage corpus* (their covered floors stayed flat). A future
  corpus refresh could bank hole-bearing terms so the generative sweep reaches them.
- v1's proof-hole trigger fires only for **argument-position** holes (`elaborate_expr_checked`);
  whole-body holes keep their pre-existing path. Design §4.1 scopes this deliberately.
