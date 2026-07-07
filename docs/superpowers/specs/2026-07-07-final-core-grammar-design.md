# Final-Core Grammar (Wave 0)

**Date:** 2026-07-07
**Branch:** `feature/idris-parity`
**Status:** design — the Wave-0 deliverable. Specifies the *entire* end-state
Core term language up front (strategy decision 4). The kernel will not *produce*
all of this until the later waves land; the validator (§J) is written against the
whole grammar and flips each clause to hard-reject as its wave completes.

## Purpose

This is the target `Cure.Core.Term` taxonomy after the dependent-kernel cleanup —
the shape every wave converges on. It fills in the field reservations decided in
the grammar brainstorm and resolves the three open grammar forks (eliminator
form, primitives, equality). It supersedes the *shape* documented in
`lib/cure/core/term.ex`'s moduledoc; that moduledoc's claim that Core "carries no
implicits, holes, or erasure annotations … fully explicit and fully relevant" is
**revised** — Core stays hole/implicit-free, but it *does* carry a per-binder
**grade** (erasure + the reserved resource axes). Relevance becomes a *checked
property under the grade*, not a blanket invariant.

Companion documents (do not duplicate; this defers to them):
- Wave ordering and per-K scope: [`audit_categorised.md`](../audit_categorised.md).
- Cross-cutting execution frame: [`2026-07-07-dependent-kernel-cleanup-strategy-design.md`](2026-07-07-dependent-kernel-cleanup-strategy-design.md).
- Effects (deliberately **out** of Core): [`2026-07-07-sound-effect-discipline-design.md`](2026-07-07-sound-effect-discipline-design.md).

## Design principles (recap, load-bearing here)

1. **Idris/Agda-shaped, not Lean-shaped** (strategy decision 5): QTT-style
   multiplicities on binders; predicative cumulative universes;
   irrelevance-via-quantity-0. Lean is a *forgetful projection* target, never the
   native shape.
2. **Uniformly strict** (decision 3): one kernel, no permissive mode. No holes,
   no universal-subtype `Any`, no unproven obligations inside the TCB.
3. **Reserve the invasive fields now, keep everything else additive** (grammar
   triage): the only Wave-0 field reshapes are the grade record on binders,
   level-expressions + level-params, and qualified symbol ids. Every deferred
   language feature is either a new additive type-former, a conversion-algorithm
   upgrade, an elaborator/surface construct, or a new axis on the (extensible)
   grade record — none of which touches an existing node's arity a second time.

## §A. The final node taxonomy

Legend for **Change**: **keep** = unchanged; **reshape** = same role, new fields
(invasive — reserved in Wave 0); **delete** = removed, role re-expressed via
another node; **new** = added node.

| Final node | Current form | Change | K / wave |
|---|---|---|---|
| `{:type, level}` — `level` is a **level-expression** | `{:type, level}` (int, 0..2) | reshape | K7 |
| `{:var, k}` | same | keep | — |
| `{:pi, grade, dom, cod}` | `{:pi, dom, cod}` | reshape (+grade) | grade |
| `{:lam, grade, dom, body}` | `{:lam, dom, body}` | reshape (+grade) | grade |
| `{:app, f, a}` | same | keep | — |
| `{:sigma, grade, a, b}` | `{:sigma, a, b}` | reshape (+grade) | grade |
| `{:pair, a, b}` | same | keep | — |
| `{:fst, p}` / `{:snd, p}` | same | keep | — |
| `{:data, sym, params, indices}` — `sym` is a **qualified id** | `{:data, name, params, indices}` (atom) | reshape (id) | K12 |
| `{:ctor, sym, args}` — qualified id; params erased (§E) | `{:ctor, name, args}` (atom, flat) | reshape (id) | K6, K12 |
| `{:case, scrut, motive, branches}` — sole eliminator; sound index-refinement + coverage rule | same shape; branch ctor names become qualified ids | reshape (id) + checker rule | K5, K12 |
| `{:global, sym, levels}` — qualified id + level args | `{:global, name}` (atom) | reshape (id, levels) | K7, K12 |
| `{:int_type}` / `{:int_lit, n}` | same | keep | — |
| `{:float_type}` / `{:float_lit, f}` | same | keep | — |
| `{:eq, ty, a, b}` | present | **delete** → inductive `Eq` (§F) | K1 |
| `{:refl, a}` | present | **delete** → ctor `refl` (§F) | K1 |
| `{:rewrite, proof, motive, body}` | present | **delete** → `case`-sugar (§F) | K1 |
| `{:prim, op, args}` | present | **delete** → delta-reducible globals (§G) | K2 |
| `{:hole, _}` | leaks in | **excluded** — never in Core (§I) | K3 |
| `{:absurd}` | present as a Core node | **delete** → empty-`case` (§H) | K4 |

Net: **17 kept/reshaped nodes, 5 deleted nodes (`:eq`, `:refl`, `:rewrite`,
`:prim`, `:absurd`), 1 excluded (`:hole`).** No new node is added — every "new"
capability rides a reshaped field or an existing node. The taxonomy *shrinks*.

## §B. Grades — the reserved binder field

Every binding site (`:pi`, `:lam`, `:sigma`) carries one `Cure.Core.Grade`. This
is the single invasive reservation that unlocks erasure now and linearity /
affinity / security / cost later without a second re-thread.

### B.1 The grade record (extensible)

```
%Cure.Core.Grade{
  usage:    Usage.t(),      # {0, ≤1, 1, ω}  — QTT multiplicity
  security: Security.t()    # element of a module-declared IFC lattice; default ⊥ (Public)
}
```

It is a **struct, not a tuple**: adding a future axis (uniqueness, cost/WCET, a
graded-effect axis) is a defaulted field addition — additive, no node-arity
change. This is the hedge that keeps four Bucket-B features additive. A missing
axis defaults to its most-permissive element (`usage: ω`, `security: ⊥`), so
un-annotated surface code elaborates to the unrestricted grade and behaves as
today.

### B.2 Usage — ordered semiring behind a module boundary

`Cure.Core.Usage` exposes the interface the kernel programs against, never the
raw carrier:

```
zero()            # 0     — erased / type-only
one()             # 1     — linear (reserved)
omega()           # ω     — unrestricted
add(a, b)         # contraction: two uses in different branches/positions
mul(a, b)         # composition: use under a binder of grade a
leq(a, b)         # sub-usage order for checking a value of grade a where b is required
relevant?(a)      # a ≠ 0  — participates at runtime
```

Carrier `{0, ≤1, 1, ω}` is fixed in the type but **only `{0, ω}` is enforced in
Wave 0** (the existing erasure relevance-check: a grade-0 binder must not appear
in a computationally-relevant position — return value, scrutinee, applied
function, present argument — per the erasure-relevance-check decision). `≤1`
(affine) and `1` (linear) are *accepted and carried* but their at-most/exactly
once checks are **stubs that pass** until the linear-types wave; the interface is
what makes turning them on additive. Semiring laws (`0·a = 0`, `1·a = a`,
distributivity) are the checked contract on any carrier the module ever grows to.

### B.3 Security — opt-in module-level IFC

`Cure.Core.Security` is a **bounded join-semilattice**, declarable per module,
defaulting to the trivial one-point lattice `{Public}` (`⊥ = Public`). Semantics
match the grammar decision:

- **Default off:** with the trivial lattice every grade's `security = ⊥`, all
  flow checks are vacuous no-ops, zero overhead.
- **Opt-in is contagious/sticky:** a module that declares a non-trivial lattice
  and labels a definition forces consumers to participate — the label rides the
  definition's type through the env, so a downstream module cannot silently
  discard it (it was "deemed important at definition time").
- **Enforcement:** the kernel rejects a flow that would move a value to a strictly
  *lower* security level (non-interference: no `High → Low`). The join tracks the
  least upper bound through elimination.
- **Declassification is explicit and audited:** the only downward move is a
  surface `declassify` form that elaborates to a marked, logged coercion; it is
  the one sanctioned hole in non-interference and is visible in the term.

Like usage, security enforcement is **carried in Wave 0, enforced when the IFC
wave lands**; the trivial default means shipping it early costs nothing.

### B.4 Kernel obligations for grades

- Well-formedness: the grade on every binder is a valid `Grade` (each axis a
  valid element of its algebra).
- Usage: on checking `{:lam, g, A, b}` against `{:pi, g', A, B}`, require
  `Usage.leq(g.usage, g'.usage)` and check the body's variable usage against `g`.
- Grade-0 relevance: the existing erasure check, generalized to read the binder's
  `usage` instead of a separate `{0,ω}` side-table.
- Security flow: LUB tracking + no-downward-flow, active only under a non-trivial
  lattice.

## §C. Universes (K7)

`{:type, level}` where `level` is a **level-expression**, not a bounded int:

```
level ::= lzero
        | lsucc level
        | lmax level level          # predicative max — NOT Lean's imax
        | lvar α                    # a bound universe parameter
```

- **Predicative & cumulative:** `Type ℓ : Type (lsucc ℓ)`; `lmax` for the
  universe of a `:pi`/`:sigma` (`Type (lmax ℓ₁ ℓ₂)`). **No `imax`, no
  impredicative `Prop`** (decision 5; Bucket C decline). Irrelevance is
  grade-0, not a `Prop` sort.
- **Level polymorphism:** globals and data families may bind universe
  parameters. `{:global, sym, levels}` carries the list of level-expression
  **arguments** instantiating those parameters at the use site; the binding
  parameters live in the global's stored signature.
- **Remove the `@ceiling 2` cap** — the hierarchy is unbounded. `term?/1`'s
  `level <= @ceiling` check is replaced by well-formedness of the level-expression
  (all `lvar`s in scope).

## §D. Symbols & identity (K12)

`:global`, `:data`, `:ctor`, and `:case` branch heads reference a **qualified
symbol id**, not a bare atom:

```
Cure.Core.Sym  ≈  %{module: [atom], name: atom}   # or an interned integer id + table
```

- **Kill `String.to_atom/1`** in `from_external/1` (unbounded atom interning =
  table-exhaustion + collision risk). Decode into `Sym` values, interned through a
  bounded symbol table.
- Identity is structural on `Sym`, so two distinct modules' `foo` never collide,
  and constructor/data resolution is unambiguous — the precondition for
  signature-driven constructor checking in §E.
- Serialization (§K) encodes `Sym` explicitly (module path + name), keeping the
  C2 external form total and collision-free.

## §E. Eliminator & recursion — Fork 2 resolved

**Decision: the sole native eliminator is the motive-carrying dependent
`{:case, scrut, motive, branches}` (a single split, non-recursive). Recursion is
definitional — a global whose body references itself (or a mutual group),
gated by the existing size-change termination certificate. Lean-style recursors
are the *encoder's* lowering target, never a native Core node.**

Rationale:

- **Consistency with decision 5.** Case-tree + a separate termination checker is
  the Agda/Idris shape; recursors-with-no-termination-checker is the Lean shape.
  We committed to the former.
- **Reuse of landed infrastructure.** The size-change termination certificate
  (`certificate.ex`, the #13/#14 work) already validates definitional recursion.
  A recursor-based core would *discard* that and re-encode every recursion as a
  recursor application — strictly more work for a poorer fit with erasure/usage.
- **Grades live naturally on `case` + definitional recursion.** Threading
  multiplicities through motive-carrying case branches is direct; through
  generated recursors it is indirect.

There is **no `fix` term node** — recursion is not a term former but a property
of the global environment (self/mutual reference), exactly as today. `:case` is
the only elimination node; `:fst`/`:snd` remain the sigma projections.

**Reframing the recent Lean-recursor commits** (`Add Lean-style {mutual,indexed}
recursor shape`, `Align recursor eliminator levels with Lean`, `Route dependent
checking through Lean backend`): that recursor-generation logic is repositioned
as **`Cure.Lean.ModuleEncoder` lowering** — Lean's core *requires* recursors, so
synthesizing them belongs in the translator (outside the TCB, decision 6), fed by
the native `case` + definitional recursion. The work is not discarded; it moves
to the correct side of the fork.

### E.1 Constructor values (K6)

`{:ctor, sym, args}` gains **family identity** from the qualified `sym` (§D),
which resolves to the constructor's stored signature — the arity split into (data
params, indices, fields). The kernel checks `args` against that signature. The
**data parameters are carried at grade 0**: present for checking and for
independent re-verification (§K), erased at runtime (zero footprint) — exactly the
QTT treatment, and why this is an erasure win rather than a cost. This resolves
K6's "flat args / lost constructor identity": `:data` already stores
`params`/`indices` separately, and `:ctor` now has the identity to consult that
split. (Representation sub-choice: keep `args` a flat spine split by the signature
— the minimal-grammar default — or make the groups structural as
`{:ctor, sym, params, fields}`. Flat-spine-plus-signature is the default; noted
for review.)

### E.2 Index refinement & coverage (K5) — the soundness-critical eliminator rule

`:case` stays structurally `{ctor, arity, body}` (**no new payload field**); the
*checking rule* is strengthened to the sound dependent-match discipline. For each
branch: instantiate the motive at the constructor's index expressions, **unify**
those against the scrutinee's actual indices, and check the body under the
resulting refinement (solved equations substituted into context and goal).
Constructors whose indices fail to unify are **impossible** and rejected/omitted;
every possible constructor must be **covered**. This closes the "branch-skipping
index unifier" divergence — today's eliminator skips the refinement, which is
unsound (it accepts branches under an unrefined context).

K5 is a **kernel typing rule**, not a structural-shape clause, so it is enforced
by the case-checker rather than the grammar validator (§J). It reuses the landed
index-unification machinery (`unify_indices`, the Agda Cycle rule, size-change).
The audit splits it K5a (acute unifier-soundness fixes) / K5b (canonical
`Eq.rec`/transport, joined with K1b); this grammar treats both as the one sound
`:case` rule.

## §F. Equality — inductive `Eq`, transport-as-sugar (K1)

Delete `{:eq}`, `{:refl}`, `{:rewrite}`. Equality becomes an ordinary inductive
family in the global environment — **the inductive `Eq`/`refl` already exist in
`builtins.ex`**, so K1 re-points to them rather than creating them (the
identity-type-as-inductive thread, task #90):

```
Eq   : (A : Type ℓ) → A → A → Type ℓ
refl : (A : Type ℓ) (a : A) → Eq A a a
```

- `{:eq, T, a, b}` ⤳ `{:data, Eq-sym, [T], [a, b]}`.
- `{:refl, a}` ⤳ `{:ctor, refl-sym, [a]}` (with `A` erased per §E).
- `{:rewrite, …}` / surface `transport` / `subst` / `J` ⤳ **elaborator sugar**
  producing a `{:case}` on the equality proof with the appropriate motive. No
  transport node survives in Core.
- **K/UIP is adopted** (decision 5, task #90): case on `refl` may collapse the
  index — this is what forecloses cubical/HoTT (Bucket C) and is the deliberate
  trade for a simpler conversion. The `K`/`J` eliminators are the two
  derived-in-surface forms; both bottom out in `:case`.

## §G. Primitives — delta-reducible globals, native int/float (K2)

Delete `{:prim, op, args}`. Two categories replace it:

1. **Primitive types & literals stay native:** `{:int_type}`, `{:int_lit, n}`,
   `{:float_type}`, `{:float_lit, f}` remain first-class term nodes. These are the
   machine-int/float builtins the ESP32 story depends on (the builtin-inductive /
   native-int foundation; `Nat` erases to native `Int`). They are **not**
   inductives.
2. **Primitive operations become typed global constants** with a trusted
   **delta-rule** reducer: e.g. `Int.add : Int → Int → Int` is a `{:global, …}`
   whose reduction fires — inside the kernel's normalizer — only on
   fully-applied literal arguments, computing the result. Applied via ordinary
   `{:app}`; no bespoke node. The delta table is a small, fixed, audited part of
   the reducer's TCB.

`Bool` and all other datatypes are real inductive families (already true) — the
primitive surface is exactly {int/float types + literals + the fixed delta-op
globals}.

## §H. Empty & absurd (K14)

`{:absurd}` is a current Core node (K4). Delete it. Ex-falso is instead the
elimination of an **empty inductive** (`Empty`, a `:data` with no constructors) via
`{:case, scrut, motive, []}` — a `case` with an empty branch list. The kernel
accepts an empty branch list **only** when the scrutinee's type is a family with
no constructors; otherwise it is a coverage error (§E.2). This removes the node
and makes "impossible" a derived, checked fact rather than a trusted marker. (The
audit's K4 also allows an *elaborator-only* marker; we take the stricter line —
absurd never appears in checked Core, only empty-`case` does.)

## §I. Explicitly excluded from Core (with where they live instead)

- **Holes** `{:hole, _}` (K3) — never in a checked Core term. They exist only in
  the elaborator's open-term representation; the validator hard-rejects any
  residual hole. `closed?/1`'s hole mention is dropped.
- **Implicits** — resolved by the elaborator before Core; Core is fully explicit
  (unchanged invariant).
- **Effects** — a *surface* discipline erased before Core (the effect spec); Core
  never sees an effect. No arrow-effect slot (Fork closed: "no").
- **`Any` as a universal subtype / implicit fallback** (K14) — banned (decision
  3). `Any` survives only as an explicit opaque dynamic type with a single
  checked-cast elimination at a declared FFI boundary; that is a normal global
  type, not a conversion hole.
- **Deleted term nodes** `{:eq}` `{:refl}` `{:rewrite}` `{:prim}` `{:absurd}` —
  re-expressed per §F/§G/§H.

## §J. The Wave-0 validator — the executable checklist

`Cure.Core.Validator` checks a term against the **full final grammar** above.
Each grammar commitment is a named clause with a mode:

- `:off` — not yet checked (legacy form still produced upstream).
- `:warn` — legacy form detected; logged, not rejected.
- `:reject` — hard error; the clause is enforced.

A clause is authored at `:warn` in Wave 0 and **flipped to `:reject` as its wave
lands** (decision 4). "Wave N done" ≡ its clauses are `:reject` and the kernel
still produces terms that pass them, with Antigen green + fixtures updated.

| Validator clause | Enforces | Flips at |
|---|---|---|
| `grade_on_binders` | every `:pi`/`:lam`/`:sigma` carries a well-formed `Grade` | Wave 0 (`:reject` immediately — new field) |
| `usage_relevance` | grade-0 binders absent from relevant positions; `{0,ω}` only | grade wave (affine/linear stay `:off`) |
| `no_eq_node` | no `{:eq}`/`{:refl}`/`{:rewrite}`; `Eq` is `:data`/`:ctor` | K1 wave |
| `no_prim_node` | no `{:prim}`; primitive ops are delta-globals | K2 wave |
| `no_hole` | no `{:hole, _}` anywhere | K3 wave |
| `qualified_syms` | `:global`/`:data`/`:ctor`/branch heads use `Sym`, not atoms | K12 wave |
| `ctor_signature` | `:ctor` args check against resolved signature; params at grade 0 | K6 wave |
| `case_coverage` | branch ctor set exactly covers the family; arities match signature | K5 wave (structural part) |
| `level_expr` | `{:type, ℓ}` is a well-formed level-expression; globals carry level args; no ceiling | K7 wave |
| `no_absurd_node` | no `{:absurd}`; ex-falso only via empty-`case` over an empty family | K4 wave |
| `no_legacy_reducer` | normal forms produced by the clean reducer only | K10 wave |

The validator checks **structural shape**, not typing. The soundness-critical
part of K5 — sound index unification and refinement per branch (§E.2) — is a
*typing* rule enforced by the kernel's case-checker, not a validator clause;
`case_coverage` above only checks the structural coverage/arity shape. Building
this validator scaffold is itself the audit's **K11a** step (Final-Core grammar +
validator), the first item in the tackle order.

The validator is thus the single source of truth for "how far the cleanup has
progressed": at any commit it names precisely which constructs remain in legacy
form.

## §K. Serialization / C2 impact

`to_external/1` + `from_external/1` (the JSON-able C2 encoding for an independent
re-checker) grow in lockstep with §A:

- Binders emit their `Grade` (both axes, with defaults elided as permissive).
- `:type` emits a level-expression tree; globals emit level args.
- `:global`/`:data`/`:ctor` emit `Sym` (module path + name), **replacing
  `String.to_atom`** with symbol-table interning on decode.
- Deleted nodes lose their encodings; `Eq`/`refl`/absurd round-trip through the
  `:data`/`:ctor`/`:case` encodings.

The encoding stays total and reversible (no PIDs/refs/closures in Core), so the
independent-checker contract holds across the reshape.

## §L. Lean projection (forgetful) — consistency note

`ModuleEncoder` lowers Final Core → Lean Core as a **forgetful map** (decision 6):
erase grades (drop usage + security), lower `:case` + definitional recursion to
Lean **recursors** (§E), map the inductive `Eq` to Lean's `Eq`, map delta-globals
to Lean primitives or `@[extern]` shims, and map the predicative universe
hierarchy into Lean's (richer) one. lean4lean then witnesses the **dependent
skeleton only** — never the quantitative layer, which is the Elixir kernel's sole
permanent responsibility. Each wave that deletes a divergence is a node the
encoder no longer has to special-case; the two forks converge as a side effect.

## Non-goals (this document)

- Not the implementation plan — that is the next artifact (writing-plans), which
  sequences the validator clause flips against the audit's wave order.
- Not a re-specification of per-wave scope — that stays in `audit_categorised.md`.
- No Bucket-B feature is designed here; §B.1's extensible record and §C's open
  level-expression are the only forward-compatibility hooks, and both are
  zero-cost today.
