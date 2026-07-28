# Mailbox-type inference — the open core as a least-fixpoint, and the shape that fills it

*2026-07-17. The research core of G9 (mailbox-type inference across evolving protocols) has
a precise mathematical shape: it is a LEAST FIXED POINT over the lattice of interfaces.
`Std.Otp.InferenceFixpoint` scaffolds that outer shape in Cure with typed HOLES for the
inner parts that are intractable today, and this note pins down the matching shape —
Lean mathlib's `Order/FixedPoints.lean` + `Order/Iterate.lean` — whose contents FILL those
holes. mathlib is cloned at `~/Develop/mathlib4` to port against.*

## The outer shape

`Std.Otp.Inference` / `Std.Otp.InferenceLaws` solved the FIRST-ORDER case: the interface is
the receive-clause set, membership is decidable, and interfaces form a subtyping order
(`AllHandled` = ⊆, with `handles_mono` monotonicity, `weaken` transitivity, `self_member`
reflexivity + principality). The OPEN case is an EVOLVING protocol, where the accepted set
at a program point depends on the interface itself (a recursive session). Inference there
is not a read-off; it is a fixpoint:

- Interfaces are a **complete lattice** (finite: the powerset of the tag universe, ordered
  by ⊆, with ⊥ = ∅ and join = ∪).
- A behaviour induces a **monotone transfer function** `f : Interface →o Interface` — from a
  candidate interface, the constraints it must then satisfy (the tags it must accept given
  what it receives and sends under that candidate).
- The **inferred interface is `lfp(f)`** — the least fixed point of the transfer.
- **Soundness** = `lfp(f)` is a fixed point (a self-consistent interface): `f(lfp f) = lfp f`.
- **Principality** = `lfp(f)` is the LEAST fixed point: any other valid interface is a
  widening of it — exactly what an inferred type should be.

This is Knaster–Tarski / Kleene. It is not a Cure-specific trick; it is THE shape of type
inference as constraint-and-fixpoint (Algorithm W, dataflow analysis, abstract
interpretation all instantiate it).

## The holes, and the mathlib theorem each one is

`Std.Otp.InferenceFixpoint` states the shape with these holes. Each is a named,
type-checked gap whose FILL is a specific mathlib result (`~/Develop/mathlib4`):

| Cure hole | What it claims | mathlib fill (`Mathlib/Order/FixedPoints.lean`) |
|---|---|---|
| `?lfp_construction` | `lfp(f) : Interface` exists | `OrderHom.lfp` — `sInf {a | f a ≤ a}` (abstract); finite version = Kleene iterate (below) |
| `?lfp_le` | `f(a) ⊆ a → lfp(f) ⊆ a` | `OrderHom.lfp_le` (`sInf_le`) |
| `?le_lfp` | `(∀ b, f(b) ⊆ b → a ⊆ b) → a ⊆ lfp(f)` | `OrderHom.le_lfp` (`le_sInf`) |
| `?map_lfp` | `f(lfp f) = lfp f` (it IS a fixed point) | `OrderHom.map_lfp` (needs `f.mono` + antisymmetry) |
| `?is_least` | `lfp(f)` is the LEAST fixed point (principality) | `OrderHom.isLeast_lfp` |

## The fill strategy — finite lattice makes it CONSTRUCTIVE

mathlib's `lfp := sInf {a | f a ≤ a}` needs infima of ARBITRARY subsets (a full complete
lattice). Cure is constructive and total; we do not want `sInf` over arbitrary predicates.
The finite tag-powerset lattice makes the fill computable by **Kleene iteration**:

- `lfp(f) = f^[h](⊥)` where `h` = the number of tags (the lattice height). The ascending
  chain `⊥ ⊆ f(⊥) ⊆ f²(⊥) ⊆ …` is monotone (Mathlib `Order/Iterate.lean`
  `monotone_iterate_of_le_map`, from `⊥ ⊆ f(⊥)`), and on a lattice of height `h` it must
  STABILIZE within `h` steps (pigeonhole: a strictly ascending chain can have length ≤ h).
  So `f(f^[h] ⊥) = f^[h] ⊥` — filling `?lfp_construction` and `?map_lfp` constructively.
- `?lfp_le`: every iterate `f^[n](⊥)` is ⊆ any pre-fixed point `a` (induction on `n`: `⊥ ⊆ a`,
  and `f` monotone preserves `⊆ a` since `f(a) ⊆ a`). Mathlib `Order/Iterate.lean`
  `iterate_le_of_le` is the same lemma; the induction ports directly. `?is_least` follows
  (`map_lfp` + `lfp_le` at fixed points, as `isLeast_lfp` composes them).

So the PORT is: take the five statements from `Order/FixedPoints.lean` verbatim (they already
match the hole signatures), and discharge them not via abstract `sInf` but via the two
`Order/Iterate.lean` iteration lemmas specialized to the finite interface lattice. The
constructive Kleene fill is strictly easier than mathlib's general version — the hard part
mathlib solves (arbitrary complete lattices) we do not need.

## The FRONTIER: where the transfer `f` comes from (and does IT have a mathlib shape?)

The fixpoint shape assumes `f` is given and monotone. `scaffolds/inference_frontier.cure`
sketches where `f` comes from: a FOLD over a behaviour syntax
(`BNil`/`BRecv`/`BSend`/`BChoice`/`BVar`/`BRec`), `transfer(b, env)`, with `env` the
interpretation of the recursion variable `BVar`; `BRec` closes the recursion with `lfp`.
This splits the frontier into two structural sub-shapes — and, surprisingly, BOTH have a
mathlib home:

1. **Interpreting recursion (`BRec`)** = the transfer's own fixpoint, needing SCOTT-CONTINUITY
   (not just monotonicity) so the ω-chain converges → **`Mathlib/Order/OmegaCompletePartialOrder.lean`**:
   `ωSup_iterate_mem_fixedPoint` (Kleene: the ω-iteration chain from `x ≤ f x` reaches a fixed
   point), `ωSup_iterate_le_fixedPoint` (it is the LEAST — principality), `ContinuousHom` (→𝒄).
   This is strictly MORE general than the finite-lattice `OrderHom.lfp` and specializes to it.
2. **Constraint generation (the fold itself)** = a CATAMORPHISM from the initial algebra of the
   behaviour functor into the algebra of continuous endo-maps of the interface lattice →
   **`Mathlib/CategoryTheory/Endofunctor/Algebra.lean`** (F-algebras). mathlib has the structure;
   assembling THIS specific algebra is a construction, not a packaged theorem.

**`?transfer_mono` (transfer is monotone) — matching shape in LEAN CORE, not mathlib.** That
each behaviour former's contribution is monotone (so the fold assembles a valid transfer whose
`BRec` `lfp` exists and is principal) is a PL-semantics obligation with no mathlib theorem —
but it has a precise match in **Lean's own compiler** (`~/Develop/lean4`, already present):
- `Init/Internal/Order/Basic.lean` — Lean's `CCPO` (chain-complete partial order) + `monotone`
  basis, the exact order-theoretic setting for partial-fixpoint definitions.
- `Lean/Elab/Tactic/Monotonicity.lean` — an EXTENSIBLE, COMPOSITIONAL monotonicity prover:
  a database (`monotoneExt`, `[partial_fixpoint_monotone]`) of per-former monotonicity lemmas
  (conclusion `monotone (fun x => e)`) that it matches against a recursive body and applies.
  This is exactly how to discharge `?transfer_mono`: ONE monotonicity lemma per behaviour
  former (`BRecv`, `BSend`, `BChoice`, `BRec`), composed — Lean does this automatically to
  admit user recursive definitions.
- `Lean/Elab/PreDefinition/PartialFixpoint/Induction.lean` — fixpoint INDUCTION (= mathlib
  `lfp_induction`), for proving properties of the inferred type.

So the frontier is MORE portable than "open": the fixpoint (existence/soundness/principality)
fills from `Order/FixedPoints` + `Order/OmegaCompletePartialOrder`; the fold's structure from
`CategoryTheory/Endofunctor/Algebra`; the transfer's monotonicity from Lean core's CCPO +
compositional-monotonicity pattern. What is left with NO external match — the ONE genuinely
novel theorem — is **domain ADEQUACY**: that `infer(behaviour)` computed this way is the mailbox
type under which the OTP reduction (`Std.Otp.Preservation`/`Safety`) is actually safe — i.e.
tying the inferred interface back to the operational metatheory already built. That connection
is the real contribution a full G9 push would make; the machinery to state and manipulate it is
all portable from the two local Lean trees.

## Artifacts

- `metatheory/otp/src/otp_inference_fixpoint.cure` — the holed outer-shape scaffold.
- `~/Develop/mathlib4` — cloned reference; port `Order/FixedPoints.lean` (statements) +
  `Order/Iterate.lean` (constructive fill) into the finite interface lattice.
