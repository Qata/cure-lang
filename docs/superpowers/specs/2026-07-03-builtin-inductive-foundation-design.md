# Builtin-Inductive Foundation — Design

**Status.** Approved design (2026-07-03). Branch `autopilot/lean-shape-matching`.
**Layer.** K (kernel/TCB) + C (erasure/codegen) + P (prelude). TCB-touching —
gated per the HARD-STOP discipline.

## Goal

Introduce a **builtin-inductive registry** so the kernel and erasure can know a
*canonical* inductive by key, then use it to (1) make **`Bool` a real inductive**
— retiring the bespoke `bool_elim` primitive into the general `:case`/recursor —
and (2) give **`Nat` an efficient native runtime representation** (`Nat → Int`),
replacing today's fatal unary encoding.

## Why (motivation)

- **Lean/Agda-class minimal TCB.** `bool_elim` is a hand-written primitive
  eliminator spread across ~8 core modules (term/value/eval/quote/conv/normalise/
  kernel/certificate) — and already sprang one conversion soundness hole. Folding
  `Bool` into the general `:case` the kernel already has removes a whole
  primitive and a class of future soundness risk. One eliminator scheme, not two.
- **Device-viable runtime representations.** Today `Nat = Z | S(Nat)` erases to
  unary nested tuples (`{:S, {:S, :Z}}`) — O(n) space. On ESP32/AtomVM a `Nat`
  loop counter or list length would exhaust RAM. The Idris "Nat hack"
  (`%builtin Natural Nat`, GMP at runtime) is the fix: erase `Nat` to a machine
  integer. This is directly load-bearing for the repo's whole reason to exist.
- **One mechanism, double duty.** The same registry lets the kernel *construct*
  canonical `Bool` (so `{:prim}` comparisons yield it) **and** lets erasure pick
  the native representation (`Bool → atom`, `Nat → int`). Building it once buys
  both the type-level and the runtime-level payoff.

## Background — current state (verified)

- The dependent kernel (`lib/cure/core`) has **no** notion of a canonical/builtin
  inductive; every inductive lives in the signature, user-declared. (`grep` for
  builtin/preloaded/canonical inductive in `lib/cure/core` finds nothing.)
- `Bool` is a **primitive**: `{:bool_type}`, `{:bool_lit}`, and the `{:bool_elim}`
  eliminator, plus `{:prim, op, args}` ops whose results are `{:vbool, _}` typed
  at `{:vbool_type}` (`kernel.ex` `infer_prim`, `eval.ex` fold).
- `Nat` is an ordinary user inductive; it erases via the generic constructor
  lowering to nested tuples/atoms (confirmed: demo output `{:S, {:S, :Z}}`).
- `{:absurd}` is rejected by the kernel in a reachable position; branches are
  discharged as vacuous only via the kernel's own index unification.

## Architecture

### 1. The builtin-inductive registry (the mechanism)

- The prelude declares the builtin types as **ordinary Cure inductives**, each
  carrying a binding to a canonical key:
  ```cure
  @builtin(:bool)
  type Bool = False | True

  @builtin(:nat)
  type Nat = Z | S(Nat)
  ```
- `@builtin(:key)` registers `key → family-id` in the signature. Registration is
  **schema-validated at seed time** against a fixed expected shape per key
  (`:bool` ⇒ exactly two nullary constructors; `:nat` ⇒ a nullary `Z` and a unary
  `S(Nat)`). A binding that does not match its schema is a hard error — so the
  kernel relies only on a *validated* binding, never on arbitrary signature data.
- `Signature.builtin(sig, :key)` resolves the family. Used by the kernel
  (`infer_prim` returns `builtin(:bool)`) and by erasure (representation choice).
- **Trust chain / why signature-seeded is sound:** the prelude inductive is
  kernel-checked like any declaration (`check_family`), *and* the `@builtin`
  binding is schema-checked, so `infer_prim`'s assumption "the thing I return has
  two nullary constructors" is doubly guaranteed. Net TCB change: **remove**
  `bool_elim` (large) and **add** the registry lookup + schema validation (small)
  → a net reduction.

### 2. Bool as an inductive (Phase 1, TCB)

- `Bool` becomes the prelude inductive above; `True`/`False` are its constructors.
- `{:prim}` ops (`:eq`,`:ne`,`:lt`,`:le`,`:gt`,`:ge`,`:and`,`:or`,`:not`) return
  `Signature.builtin(sig, :bool)` instead of `{:vbool_type}`, and their evaluation
  produces the corresponding constructor value instead of `{:vbool, _}`.
- Surface `true`/`false` literals elaborate to the `True`/`False` constructors.
- `if` / `when` guards / literal-pattern desugarings **retarget** from
  `{:bool_elim, …}` to `{:case, …}` on `Bool` (a 2-constructor family the kernel
  already covers — coverage, motive, and branch conversion all handled).
- **Retire** `{:bool_type}`/`{:bool_lit}`/`{:bool_elim}` and their eight core-module
  clauses; keep `{:prim}` (the ops themselves stay — only their result *type* and
  *value* become the inductive Bool).
- **Erasure:** `False`/`True` lower to the native lowercase atoms `false`/`true`
  (one registry rule — Cure constructors are capitalized but BEAM booleans are
  lowercase). A `:case` on `Bool` lowers to a BEAM `case` on those atoms — which
  is exactly what `{:prim}` comparisons already return, so construct/match/prim
  are self-consistent at runtime with essentially no special erasure work.

### 3. Nat → Int runtime erasure (Phase 2, untrusted C-layer)

- Kernel is **unchanged** — it keeps checking and reducing `Nat` as the inductive
  (type-level Nats are small; no GMP kernel acceleration in v1). This is purely an
  erasure/codegen representation choice, *below* the kernel.
- Registry-driven representation selection in erasure/emit for the `:nat` builtin:
  - `Z()` ⇒ `0`; `S(n)` ⇒ `n + 1`.
  - `match n | Z() -> a | S(m) -> b` ⇒ `case n of 0 -> a; _ -> (m = n - 1; b)`.
  - `Nat`-typed `{:prim}`/arithmetic ⇒ the machine integer op.
  - `S`/`Z` used as first-class values ⇒ the increment / zero closures.
- **Soundness placement:** untrusted. The kernel already accepted the term against
  inductive `Nat`; erasure only chooses a representation. A bug here yields a wrong
  *runtime value*, never an unsound acceptance. Verified by BEAM execution + the
  differential oracle + a **representation-agreement property**: erased-Nat
  evaluation must agree with inductive-Nat evaluation on a generated corpus.
- Index-only `Nat` (e.g. `Vector(a, n)`) is erased entirely, so runtime `Nat`
  values arise only where `Nat` is computationally-relevant data — the rep applies
  cleanly there.

## Data flow

Compile-time: kernel checks terms against the *inductive* `Bool`/`Nat`. →
Erasure: registry picks the *native* representation (`Bool → atom`, `Nat → int`).
→ Runtime: BEAM atoms/integers. The inductive is a checking-time fiction; the
machine value is native.

## Phasing (each independently landable + verified)

- **Phase 1 — registry + Bool-as-inductive (TCB, GATED).** Build the registry +
  schema validation; move `Bool` to the prelude; rewire `{:prim}` results; retarget
  `if`/guard/literal desugarings to `:case`; delete `bool_elim`. Gate: red-green +
  a new Antigen antibody (binding-validation rejects a malformed `Bool`; `:case`-on-
  `Bool` equates no distinct normal forms the old `bool_elim` did/didn't) + full
  Antigen + full suite + independent adversarial review.
- **Phase 2 — Nat → Int erasure (untrusted).** Registry-driven rep selection in
  erase/emit; representation-agreement property; BEAM + oracle verification. No
  kernel change, so no TCB gate — but still red-green + full suite.

## Testing

- **Oracle:** existing `cond`/`guard`/`match` clusters must stay accept/accept
  after the Bool migration (behavior-preserving); a new probe exercises efficient
  `Nat` arithmetic and confirms the integer representation on the BEAM.
- **Antigen:** antibody for binding-schema validation (malformed `Bool` rejected);
  antibody that the `bool_elim → :case` migration preserves normal forms and
  termination certification.
- **Property:** Nat representation-agreement (erased vs inductive evaluation).
- **Full suite** once, alone, at each phase gate; **adversarial review** for
  Phase 1 (kernel-touching).

## Deferred / committed next

- **Match-embedded `when` (general)** — constructor-pattern guards woven into the
  pattern matrix + fall-through, plus Z3 as an **untrusted** coverage lint
  (trichotomy drops the catch-all; non-exhaustive errors; shadowed warns). The
  variable-pattern subset already landed (`92d11d5`). This is the immediate
  follow-on once the foundation lands, and it must be built on inductive-`Bool`
  `:case`, not `bool_elim`. (Roadmap §4.2.)

## Out of scope

- `Int`/`Float`/`String` as inductives — irreducibly primitive BEAM machine types.
  `Int` stays a **distinct** type from `Nat` (`0 : Int` vs `Z() : Nat`); integer
  literals remain `Int`.
- GMP/native kernel acceleration of `Nat` reduction — v1 reduces `Nat`
  inductively; only the *runtime* representation changes.
- A user-facing `@builtin` pragma as a general language feature — the mechanism is
  internal (prelude-only) for now.
- Trusting Z3 in the dependent kernel — locked out (see the SMT trust-boundary
  decision); unrelated to this work but restated so scope is total.

## Risks + mitigations

- **Bootstrapping.** `{:prim}`/erasure need the canonical `Bool`/`Nat` seeded.
  Mitigation: the prelude always seeds them; a `{:prim}` reached without the
  binding is an explicit early compiler error, never a silent miscompile.
- **Migration churn.** Retiring `bool_elim` touches code committed earlier this
  run (`if`/guards/literals). Mitigation: the retarget is mechanical
  (`{:bool_elim,…}` → `{:case,…}`), covered by the existing green tests, gated by
  the full suite.
- **Literal ↔ constructor wiring / capitalization.** `true`/`false` literals must
  resolve to `True`/`False` constructors and erase to lowercase atoms; covered by
  the registry rule and an explicit test.
