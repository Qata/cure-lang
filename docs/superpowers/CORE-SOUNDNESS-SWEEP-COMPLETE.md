# Core soundness sweep complete — decision needed on the parity reshapes

**Date:** 2026-07-08 · **Branch:** `feature/idris-parity` · **Gate:** `mix test` green (3079 passed)

The unattended Core-cleanup cron has assessed **every** audit K-item. This is the
consolidated status and the one decision that needs you.

## Bottom line

**The Core is soundness-clean.** Every genuine soundness/boundary tightening the
audit called for is landed and gated. What remains is **not** soundness work — it
is one coherent **grade + representation modernization** that is faithfulness/parity,
deeply coupled, and (by your own "features need design approval" rule) deserves a
design pass rather than incremental cron surgery.

## Landed (real soundness/boundary tightenings)

| Item | What |
|------|------|
| K3 | Holes firewalled out of final Core (`no_hole` → reject) |
| K5a | Index-unifier soundness: length guard, `unify_spine` mismatch → `:impossible` |
| K13 | SMT/refinement obligations fail-closed (Z3 out of TCB, lint-only) |
| K14 | No gradual `Any` in dependent/final mode (enforced by construction) |
| K4 | `{:absurd}` → empty-`case` ex-falso; node gone from produced/final Core |
| K2 | Partial-op non-reduction pinned (div/rem/float-div by zero stay neutral) |
| K12 (slices 1–2) | Bounded symbol interning at both decode boundaries (atom-table-DoS fix) |
| K10 (#12) | `dependent?/1` misclassification proven **fail-safe** (implicit-arg arity barrier) |

## Deferred / declined **with recorded proof** (faithfulness/parity, not soundness)

- **K6** — constructor params riding the spine (grade-0). *Grade-coupled.*
- **K12 (Sym)** — full qualified-symbol representation. *Collision-freeness already
  delivered by the E-layer; migration is cleanliness.* (Plus a genuine **E-layer**
  finding filed: cross-module same-named **globals** silently overwrite —
  `global-def-collision-gap`, out of Core scope.)
- **K7** — universe polymorphism / level-expressions. *Current system is sound
  (predicative, cumulative, two-universe rule); the rest is expressiveness.*
- **K1 / Eq (Phase B/C)** — retire primitive `{:eq}/{:refl}/{:rewrite}`. *Phase A
  landed (refl-matching works, the observable symptom is fixed); B/C is faithfulness
  and is **blocked by K6*** (bridge_step needs an inferable `refl`, which the
  inductive ctor can't provide until K6's param-in-spine lands).
- **K5b** — canonical transport; joined with K1b, rides the Eq cluster.
- **K10 (legacy Pi/Sigma/Reduce)** — never used to check dependent programs
  (delegated to Core); cleanliness-to-delete.

## The coupling

Everything deferred traces to **two coupled foundations that aren't built yet**:
the **QTT grade machinery** (0/ω, in-scope per "minus linear types" but *not* a
numbered wave) and the **qualified-`Sym` representation**. K6 needs grades; Eq-B/C
needs K6; K7 and K12-Sym are the same modernization. None buys soundness.

## Decision needed (I've paused — not auto-proceeding)

1. **Start the grade wave** — build the 0/ω grade machinery, which unblocks K6 →
   Eq-retirement and clears K7. Biggest lift; completes true Idris-parity of the
   representation.
2. **Fold the reshapes into the deferred "gaps"** — treat them as design-gated
   features (brainstorming → design → approval), alongside unsafe-hole taxonomy /
   Bucket B/C / FRP.
3. **Accept the soundness-clean Core as-is** and proceed straight to the deferred
   gaps.

I did **not** auto-start the gaps or the grade wave, because the strategy above is
your call and the situation is more nuanced than the cron's linear
"all-landed → start-gaps" assumption. Full rationale per item lives in
`docs/superpowers/audit_categorised.md` (each K section) and the specs.
