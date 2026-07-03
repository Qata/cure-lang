# Finding: `Cure.Core.Normalise` non-idempotence on context-closing lambdas

**Date:** 2026-07-04
**Surfaced by:** Antigen Tier-B reach expansion, Task 3 (Π/Σ goal seeds)
**Assay:** `term/normalization` (differential trio, `lib/antigen/assays/term.ex`)
**Severity:** HIGH — non-idempotence / non-confluence in the **trusted kernel** (TCB)
**Status:** BANKED (fixture + violation-asserting test). Fix DEFERRED — needs an operator decision + its own red-green cycle.

---

## Summary

Adding top-level **Π (Pi) goal seeds** to the Tier-B generator menu made the
`term/normalization` differential assay fail on ~5% of Pi challenges. The assay
checks the kernel invariant **`nf(nf t) = nf(t)`** (idempotence of the normal
form). On the failing terms it does not hold: the normal form **oscillates with
period 2** —

```
nf(t)      = NF1
nf(NF1)    = NF2   ≠ NF1
nf(NF2)    = NF1        ← back to NF1
nf(NF1)    = NF2   …    (period-2 cycle)
```

The two normal forms `NF1`/`NF2` are identical in structure except that a pair of
**context de Bruijn indices is transposed** (observed: `1 ↔ 3`). Concretely, in a
stuck `case` whose scrutinee is a neutral context variable, the scrutinee's index
and a branch body's index swap on each renormalization:

```
NF1:  {:case, {:var, 3}, motive, [{:T, 0, {:var, 1}}, {:F, 0, …}]}
NF2:  {:case, {:var, 1}, motive, [{:T, 0, {:var, 3}}, {:F, 0, …}]}
```

This is a genuine bug in `Cure.Core.Normalise` (the reification / quote depth
accounting for stuck-`case` branches under nested binders), **not** an Antigen
harness artifact:

- The offending term is **well-typed** — `Kernel.infer(ctx, term)` returns
  `{:ok, _}`. A sound normalizer must be idempotent on well-typed terms.
- The assay calls `Normalise.nf(ctx, ·)` **identically** on `t` and on `nf(t)`;
  a deterministic function returning two different results on the same input in
  the same context is the defect itself.
- It reproduces deterministically from a frozen fixture (below).

## Trigger conditions (measured)

Reachability by goal shape, over 1500 `term/normalization` challenges drawn with
the generator's own random contexts:

| goal shape        | oscillations |
|-------------------|--------------|
| original (Nat/Bd/Vec) | **0 / 771** |
| `List(A)`         | **0 / 290** |
| `Σ` (Sigma)       | **0 / 160** |
| **`Π` (Pi)**      | **15 / 279 (~5.4%)** |

Only **top-level Π goals** trigger it, and only with a **non-empty context**:
the same Pi intro rule generated in the *empty* context is clean (0/200). The
necessary ingredients are (a) a top-level lambda (from a Pi goal) that (b) closes
over **context variables**, reached (c) through **global-definition unfolding**
(`plus`/`dbl` δ-reduction) inside nested `case` scrutinees. Remove any one and the
oscillation disappears — which is why it lay dormant until Pi goals existed:
before this expansion the menu never produced a top-level context-closing lambda.

## Reproduction

Frozen fixture: `test/antigen/fixtures/nf_oscillation_pi.exs` — a captured Pi
challenge (context depth 4: `[Bd, Vec(v0), Nat, Bd]`, goal `Π Nat. Nat`). Loaded
and asserted in `test/antigen/assays/term_test.exs`:

```
test "banked finding: Normalise non-idempotence on a frozen Pi challenge …"
  → asserts  A.run(c) == {:violation, {:not_idempotent, nf1, nf2}}
  → asserts  Kernel.infer(ctx, term) == {:ok, _}   (term is well-typed)
  → asserts  nf3 == nf1                             (period-2, not one-shot)
```

A minimal hand-reduction was attempted but not found in-budget; the frozen
generator term is the reproduction of record. Minimization is a good first step
for whoever takes the kernel fix — the transposition insight above (stuck-`case`
branch quote depth) is the place to look first.

## Containment (what shipped)

Disciplined, non-weakening containment — the same pattern used for the two
untrusted-machinery findings (erase/2 non-idempotence, parse_model truncation):

1. **The `term/normalization` assay is unchanged and fully strict.** It correctly
   detects the bug; nothing about its detection was softened.
2. **Only the Π *menu seeds* are withheld** from `SigMenu.goal_types/0` — the
   generator is scoped away from a known-broken kernel path, so the differential
   trio stays green. The Π *intro rule* still works and keeps its unit test
   (`gen_term over a Pi goal produces a lambda`), so Pi generation is retained;
   only its use as a random top-level differential seed is paused.
3. **The finding is banked as a red-green target.** The fixture test asserts the
   violation today; when the normalizer is fixed it **flips to `:ok`**, exactly
   like the erase/parse_model regression guards did after their fixes.
4. **`List(A)` and `Σ` seeds shipped** (proven clean, 0 oscillations) — the
   reach-expansion still delivered real menu breadth.

## Recommended next step (operator decision)

Fix `Cure.Core.Normalise`'s stuck-`case` reification depth accounting, guided by
the transposition signature. Per the standing `tcb-change-blanket-approval`, a
correctness fix that aligns the normalizer with standard NbE (Agda/Lean quote
semantics) is pre-approved — but it is a TCB change that warrants its own
isolated red-green cycle (minimize → fix → confirm the fixture flips to `:ok` →
re-add the Π seeds → confirm the trio stays green over Pi at scale). That is a
separate effort from this generator-expansion initiative and is surfaced here for
scheduling.
