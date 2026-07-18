# Int Refinement Prelude (decidable-boolean reflection) — Design

**Date:** 2026-07-18
**Status:** Approved direction (operator: "Do it"); building TDD via the differential oracle.
**Layer:** Stdlib (`lib/std/*.cure`) + oracle fixtures + example re-refinement. **No kernel (K) change. No elaborator (E) change expected.**

## 1. Goal

Close the one real gap between the restored proof-backed refinement surface and
feature parity with the deleted SMT refinements: **refinements are usually stated
over `Int`, but the proposition/lemma prelude is entirely over `Nat`.** Today
`Std.Proof.Math` proves `IsPositive`/`IsLessThan(OrEqual)` only for `Nat`, so an
`{n: Int | …}` refinement — the common case, and what every deleted example used
(`dependent_types`, `motif`, `moneta`) — has no foundation to discharge against.
Those examples currently sit as plain `Int` aliases with "unchecked pending
SMTCoq" comments. This builds the Int foundation and re-refines them as the
acceptance demo.

## 2. The Nat-vs-Int decision (the gating question §5.1 flagged)

`Int` in Cure is a **primitive** (`{:int_type}`, native BEAM integer), not an
inductive. There is no structural induction on it, which is exactly why the
classic-deletion spec called Int "proof-hostile vs Nat." Two candidate routes:

- **(A) Nat-bridge** — map `Int → Nat` and reason on `Nat`. Rejected: requires
  `IntToNat`/`NatToInt` with round-trip lemmas, and the kernel still cannot
  *compute* on an abstract `Int`, so the bridge buys nothing for the abstract
  case while taxing the closed case (which already computes fine).
- **(B) Decidable-boolean reflection (CHOSEN)** — reflect the primitive
  comparison, which already returns the inductive `Bool`, into a proposition.
  This is the idiom **all three reference languages use for primitive integers**:
  Idris `So : Bool -> Type` / `Oh : So True`; Agda `T : Bool -> Set`; Lean
  `Decidable` + `decide`. It aligns with the north star and needs no kernel work.

**Why (B) is sound and computes — verified against source, not assumed:**
`lib/cure/core/eval.ex:341` — `vbool(true) = {:vctor, :"Std.Bool#True", []}`. A
closed comparison like `5 > 0` folds to the *inductive* `True()` constructor
value. So a proposition indexed by that Bool — `IsTrue(5 > 0)` — normalizes to
`IsTrue(True())`, and its sole constructor `Confirmed : IsTrue(True())` inhabits
it **by pure computation** (whnf + delta — path 1 of the deletion spec). No
solver, no postulate, no kernel change.

## 3. Surface

New module `Std.Proof.IntMath` (sibling to `Std.Proof.Math`; Nat stays where it
is). Descriptive names per the standing naming directive — the Idris `So`/`Oh`
become `IsTrue`/`Confirmed`.

```
mod Std.Proof.IntMath
  use Std.Bool
  use Std.Int       # `>`, `>=`, `<`, `<=`, `==` on Int → Bool
  use Std.Decision

  ## Evidence that a decided Boolean condition holds. The reflection primitive:
  ## a closed condition reduces to True() and is inhabited by computation; an
  ## open condition is carried as evidence by whoever constructs the value.
  type IsTrue indices (claim: Bool)
    Confirmed : IsTrue(True())

  ## Int refinement predicates, each reflecting the primitive comparison.
  fn is_positive(n: Int) -> Type = IsTrue(n > 0)
  fn is_non_negative(n: Int) -> Type = IsTrue(n >= 0)
  fn is_non_zero(n: Int) -> Type = IsTrue(n != 0)
  fn is_in_range(low: Int, high: Int, n: Int) -> Type = IsTrue(and(low <= n, n <= high))

  ## Decide a condition, carrying evidence in the Yes branch (Nat-style ergonomics).
  fn decide_is_true(claim: Bool) -> Decision(IsTrue(claim)) = match claim
    True()  -> Yes(Confirmed())
    False() -> No(fn(evidence) -> absurd_true_is_false(evidence))
```

If a `fn … -> Type` predicate proves awkward as a refinement `predicate:` slot
during TDD, the fallback is to inline `IsTrue(n > 0)` directly at the refinement
site — the surface `{n: Int | IsTrue(n > 0)}` needs no wrapper. Slice 1 decides
this empirically.

## 4. Scope boundary (the honest limit, unchanged from SMT)

- **In scope — discharges by computation:** any refinement whose obligation is
  closed at the constructing site — literals (`Percentage` of `50`), and
  binder-carried evidence threaded through (`scale`'s `factor` carrying
  `IsTrue(factor > 0)`). This is the bulk of what the examples need.
- **Out of scope — deferred to the §5.2 verified linear decision procedure:**
  abstract *quantified* Int arithmetic lemmas, e.g. `∀ a b. a>0 → b>0 → a*b>0`
  over primitive `Int`. These are **not constructively provable** over a
  primitive integer without induction, and are exactly the nonlinear
  `th-lemma`-with-no-certificate case the deletion spec noted SMT could not
  soundly discharge either. Deferring them is parity, not regression. The
  auto-lemma search's solver seam (auto-lemma spec §4.2) is where that procedure
  later slots in, behind the same trigger, with nothing here rewritten.

This asymmetry is the whole point of §5.1: closed/decidable Int facts get full
automation now; abstract nonlinear Int facts wait for the decision procedure —
and Nat retains structural-induction lemmas (`Std.Proof.Math`) for the abstract
cases that *can* route through Nat.

## 5. Testing strategy (TDD, differential oracle where it applies)

Strict red→green per slice, behavioral and immutable once green.

1. **`IsTrue`/`Confirmed` + computation** — paired `test/oracle/refine/int_is_true.{cure,idr}`
   (`.idr` uses `Data.So`/`Oh`), relation `same`. Cure unit test: a closed
   `IsTrue(5 > 0)` type-checks with `Confirmed()`; `IsTrue(5 < 0)` is rejected.
2. **Predicates + closed refinement** — `refine(50, Confirmed())` at
   `{p: Int | is_in_range(0, 100, p)}` type-checks; out-of-range literal rejected.
3. **`decide_is_true`** — returns `Yes`/`No` with evidence; unit test both branches.
4. **Binder-carried evidence** — a function taking `{n: Int | is_positive(n)}` and
   threading the evidence (the `scale` shape) type-checks.
5. **Example re-refinement (acceptance)** — `dependent_types.cure` `Positive`/
   `Percentage`, and `moneta.cure` `scale`'s `factor`, move from plain `Int` +
   "unchecked" comment to real `{… | …}` refinements; each project's own
   `mix test` + `cure.check.examples` stays green (the `dependent_types` `@expected`
   row must stay byte-identical or STOP).
6. **Full gate once, alone** — `mix test --include slow` + `mix antigen` + oracle replay.

## 6. Files

- Create: `lib/std/proof_int_math.cure`, `test/cure/stdlib/proof_int_math_test.exs`,
  `test/oracle/refine/int_is_true.{cure,idr}` (+ verdicts entry).
- Modify: `examples/dependent_types.cure`, `examples/cure_moneta/cure_src/moneta.cure`
  (and `motif.cure` if its ranges reduce to closed checks), dropping the
  "unchecked pending SMTCoq" comments for the re-refined sites.
- **Untouched:** `lib/cure/core/*` (K), `lib/cure/elab/*` (E). If either needs a
  change, STOP and report — that is a scope violation.

## 7. Non-goals

- No decision procedure / omega (that is §5.2, ledgered).
- No Nat↔Int bridge lemmas.
- No new refinement *surface* syntax (the `{x: T | φ}` grammar already exists).
- No change to `Std.Proof.Math` (Nat) beyond what re-refinement forces.
