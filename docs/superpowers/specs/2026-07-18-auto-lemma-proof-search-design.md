# Automatic Lemma Application / Proof Search — Design

**Date:** 2026-07-18
**Status:** Approved design; ready for implementation plan.
**Layer:** Elaborator (E) only — `lib/cure/elab/*`. No kernel (K) change. No TCB change.

## 1. Goal

Make proof obligations over refinement types discharge without the author naming
the lemma. Concretely, the demo goal:

```
type PositiveNatural = {value: Nat | IsPositive(value)}

fn multiply_positive(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
  refine(multiply(refined_value(left), refined_value(right)), ?)
```

Today the second argument to `refine` must be written by hand as
`multiplying_positive_numbers_is_positive(refinement_proof(left), refinement_proof(right))`.
The goal is that the author leaves a proof hole (`?`) and the elaborator *finds*
that term — so that "positive times positive is positive" discharges
automatically, and adding a new such fact is a matter of tagging a lemma, not
editing the compiler.

## 2. Non-goals (v1)

- No syntax-directed arithmetic decision procedure (Lean-`omega`-style). That is a
  *future solver* behind the same dispatch seam, wanted only if lemma search
  proves too slow or we need decision-procedure completeness.
- No discrimination-tree indexing of the lemma registry. v1 indexes by
  conclusion head and filters by unification.
- No overlap/incoherence pragmas, no default-hint (`%defaulthint`) fallback.
- No term-equality dedup of ambiguous candidates. v1 treats "two or more distinct
  candidates" as a hard ambiguity error (see §6).
- No general multi-solver arbitration policy beyond "try registered solvers in
  order; each solver is unique-or-defer."

These are deliberately deferred so v1 is the smallest thing that ships the demo
with a load-bearing, honest red→green.

## 3. Soundness stance

The resolver lives entirely in the untrusted elaborator (E). It assembles a Core
proof term and hands it to the existing kernel checker exactly as if the author
had written it. If the resolver produces a wrong term, the kernel rejects it; the
resolver cannot make an ill-typed program type-check. Therefore this feature is
**soundness-neutral by construction** — no change to `lib/cure/core/*`, no TCB
review gate, no HARD-STOP. Proofs carry grade 0 (erased), so a found proof has
zero runtime cost; it exists only to satisfy the kernel at compile time.

This stance is what the reference survey confirms is the right one: Idris, Agda,
and Lean all re-check the found/produced term in the kernel rather than trusting
the search. We inherit that property for free because search runs before the
kernel, not inside it.

## 4. Architecture

Three E-layer pieces plus two one-line surface touchpoints.

### 4.1 The trigger — proof-position holes

We do **not** introduce Idris's `{auto p: P}` syntax (Cure's named-implicit
surface is thin). Instead we reuse the existing proof hole. A `?` in a
proof-carrying position already elaborates to a `{:hole, name}` term
(`declarations.ex:1039`), and the elaborator already has a `:hole_goal`
diagnostic that computes the type a hole must be filled with
(`program.ex:1113`). We make the elaborator, at the point where a proof-position
hole's goal type is known, **attempt auto-resolution before falling through to
the unsolved-hole path**:

- resolution succeeds → the `{:hole, _}` term is replaced by the found Core proof
  term, and elaboration continues as if the author wrote it;
- resolution fails (`:none`) → the existing unsolved-hole / `:hole_goal`
  behavior is unchanged.

This is purely additive: no existing program changes behavior, because a program
that previously left an unsolvable proof hole still leaves one.

### 4.2 The dispatcher and solver seam

A new module `Cure.Elab.ProofSearch` exposes:

```
resolve(goal_type, local_context, env) :: {:ok, core_term} | :none
```

`resolve/3` consults a fixed, ordered list of **solvers**. A solver has the same
shape as `resolve/3`. This ordered list is the "C-staging" seam: v1 registers
exactly one solver (the tagged-lemma resolver, §4.3); the future syntax-directed
decision procedure would be appended here without touching the trigger or the
registry. Solvers are tried in order; the first that returns `{:ok, term}` wins.
(Because each solver is internally unique-or-defer, "first solver wins" does not
reintroduce order-sensitivity *within* a proposition domain — it only orders
*disjoint* solver strategies.)

### 4.3 Solver #1 — the tagged-lemma resolver

Two halves: a registry and a resolution procedure.

**Registry.** A theorem tagged `@lemma` is collected during elaboration and
indexed by the *head of its conclusion type*. For

```
@lemma
fn multiplying_positive_numbers_is_positive({left}, {right},
      left_is_positive: IsPositive(left), right_is_positive: IsPositive(right))
   -> IsPositive(multiply(left, right)) = ...
```

the conclusion head is `IsPositive`, so this lemma is filed under `IsPositive`.
The registry lives in the elaboration environment alongside the existing
interface/coherence registries, keyed by conclusion-head atom to a list of lemma
entries. Each entry records the lemma's global name, its full Pi type (so
hypotheses and their types are recoverable), and its arity.

`@lemma` is a decorator in the existing `{:decorator, [name: :lemma], args}`
shape (`declarations.ex:2304`). It is recognized in `declarations.ex` at
definition-processing time and its bearer registered. `@lemma` takes no
arguments in v1.

**Resolution.** Given goal `IsPositive(multiply(a, b))`:

1. Look up all registry entries whose conclusion head matches the goal head
   (`IsPositive`).
2. For each candidate, unify the candidate's conclusion type against the goal.
   Unification instantiates the lemma's implicit binders (here `{left} := a`,
   `{right} := b`).
3. For each candidate that unifies, its explicit hypotheses become **sub-goals**
   (`IsPositive(a)` and `IsPositive(b)`), each solved by a recursive
   `resolve/3` call.
4. If every sub-goal is solved, the candidate yields a Core application term:
   the lemma applied to the instantiated implicits and the sub-goal proof terms.

**Local-context path.** In parallel with the registry lookup, the resolver
searches the local context for a hypothesis whose type matches the goal. This is
what supplies the *leaves* of the demo — see §5. If a local hypothesis (or a
projection of one) has the goal type, it is a candidate term directly.

Local and registry candidates are pooled and subjected to the same
unique-or-defer discipline (§6).

## 5. The refinement leaf-proof requirement

In `multiply_positive(left: PositiveNatural, right: PositiveNatural)`, the
sub-goals the multiply lemma needs — `IsPositive(refined_value(left))` and
`IsPositive(refined_value(right))` — are **not** loose variables in scope. A
refinement type `{value: a | P(value)}` desugars to a dependent pair
`Sigma(v: a, P(v))`, so the proof is the *second projection* of the argument:
`refinement_proof(left) : IsPositive(refined_value(left))`.

Therefore the local-context search must be able to **project the carried proof
out of a refinement/Sigma-typed local**: for each local binder whose type is a
refinement/Sigma, consider its second projection as a candidate term, with the
type obtained by substituting the first projection into the pair's second
component. This is the one non-obvious piece of "build the capability," and it is
required for the demo to close end-to-end. v1 scopes this to a single level of
projection (the proof component of a refinement argument); nested/iterated
projection is not needed for the demo and is out of scope.

## 6. Resolution discipline and termination

**Discipline — Agda's, not Idris's.** The reference survey is decisive here.
Idris's default constructor/hint group is first-wins and order-sensitive: if two
hints match, it silently takes whichever was registered first, and the result can
depend on import order (`AutoSearch.idr` `anyOne`, `ambigok=True`). Agda instead
collects *all* candidates, requires them to collapse to a single survivor, solves
on exactly one, errors on zero, and **defers/errors rather than guessing** on two
or more (`InstanceArguments.hs` `findInstance'`). Cure's typeclasses are already
coherence-based, so we take Agda's discipline:

- exactly one candidate produces a well-typed term → use it;
- zero candidates → `:none` (the solver declines; the dispatcher tries the next
  solver, then the trigger falls through to the unsolved-hole path);
- two or more distinct candidate terms → **hard ambiguity error** naming the
  competing lemmas/hypotheses.

v1 uses the simple rule "≥2 distinct candidate terms → ambiguous." The
term-equality dedup that lets two candidates producing the *same* proof coexist
(Agda's `dropSameCandidates`, Idris's `nubBy`) is deferred; with a single tagged
lemma it never arises.

**Backtracking with state save/restore.** Each candidate is tried against a saved
elaborator state and rolled back on failure, so a candidate that unifies its
conclusion but fails a sub-goal does not corrupt state for the next candidate
(Idris's `successful`, Agda's `filterResettingState`).

**Termination.** Two guards, mirroring the references:

- a **depth bound** on recursive `resolve/3` calls (a fixed constant in v1). The
  demo is shallow: one lemma application (the multiply lemma) whose two
  hypotheses resolve directly from local context (§5), so search descends only a
  couple of levels. The bound exists to stop a pathological lemma set, not
  because the demo needs depth.
- a **"trying" stack**: before recursing on a sub-goal, push its type; if a
  sub-goal's type is already on the stack (up to conversion), abandon that branch
  (Idris's `abandonIfCycle`). This prevents a self-referential or mutually
  recursive lemma set from looping.

Exceeding the depth bound or hitting a cycle makes that branch fail (`:none`),
not crash — search simply reports it could not find a proof.

## 7. Surface summary

- **Trigger:** `?` proof hole in proof-carrying position (existing surface;
  behavior extended additively).
- **Registration:** `@lemma` decorator on a theorem (new; fits existing decorator
  shape). No arguments in v1.

No other surface change. Exact hook site for the trigger (where the
proof-position hole's goal type becomes available) is pinned down in the
implementation plan against `declarations.ex` / `program.ex`.

## 8. Testing strategy (TDD)

Three layers, in this order.

### 8.1 Build the capability (E-level unit tests)

Unit-test `Cure.Elab.ProofSearch.resolve/3` in isolation, independent of the
`.cure` surface:

- registry lookup by conclusion head returns the tagged lemma;
- conclusion unification instantiates implicits correctly;
- a hypothesis in the local context of the goal type is found directly;
- a refinement/Sigma local yields its proof projection as a candidate (§5);
- unique-or-defer: zero candidates → `:none`; two distinct → ambiguity error;
- termination: a cyclic goal stack abandons the branch; depth bound respected.

### 8.2 Red — the capability is gated on the tag

A `.cure` program that leaves the proof hole in `multiply_positive`, with **no
`@lemma` tag** on `multiplying_positive_numbers_is_positive`, must fail
elaboration with an unsolved proof hole. Assert the failure. This proves the hole
is not trivially discharged and that resolution is genuinely gated on the tagged
lemma — without it, there is nothing to find.

### 8.3 Green — tagging the lemma discharges the hole

Add `@lemma` to `multiplying_positive_numbers_is_positive`. Its two hypotheses,
`IsPositive(refined_value(left))` and `IsPositive(refined_value(right))`, resolve
from the refinement projections in local context (§5), so no other lemma needs
tagging — `adding_to_a_positive_number_is_positive` is used inside the multiply
lemma's already-written body and is never re-derived by search. The same program
now elaborates: the hole is filled and the kernel accepts. Assert:

- elaboration succeeds and the program type-checks;
- **the found term matches the hand-written proof** via a Core-term golden (the
  same technique as the quasiquote golden gate) — proving search found the
  *right* proof, not merely *a* term that happens to check.

### 8.4 Regression

- The full existing suite stays green (the trigger is additive; no prior program
  leaves an auto-resolvable proof hole today).
- The MetaAST conformance tripwire stays green (no new meta node tags; `@lemma`
  is an ordinary decorator).

## 9. Files (indicative; finalized in the plan)

- **Create:** `lib/cure/elab/proof_search.ex` — `resolve/3`, the solver list, the
  tagged-lemma solver, local-context + refinement-projection search, discipline,
  termination guards.
- **Modify:** `lib/cure/elab/declarations.ex` — recognize `@lemma`, register the
  tagged lemma into the elaboration environment.
- **Modify:** the proof-hole elaboration site (`declarations.ex` / `program.ex`)
  — call `resolve/3` before the unsolved-hole fall-through.
- **Modify:** `lib/std/proof_math.cure` — add `@lemma` to the two lemmas (this is
  the green step; the red step is the same file *without* the tags).
- **Modify:** `lib/std/refine.cure` — rewrite `multiply_positive` to leave the
  proof hole.
- **Create tests:** E-level resolver unit tests; a red/green elaboration test over
  the `.cure` demo; a Core-term golden for the found proof.

## 10. Reference grounding

The design is grounded in the vendored `reference/` snapshots:

- **Idris2** (`Core/AutoSearch.idr`): supplies the *trigger* model (a delayed
  hole retried during unification, target = the hole's type) and the
  *cautionary* determinism story (first-wins constructor group is
  order-sensitive) that we deliberately do not inherit.
- **Agda** (`TypeChecking/InstanceArguments.hs`): supplies the *resolution
  discipline* — collect all candidates, unique-or-defer, never order-dependent
  first-wins — and the termination shape (considering-instance deferral + depth
  ceiling).
- **Lean4** (`Elab/Tactic/Omega`, `LabelAttribute.lean`, `Simp/Attr.lean`):
  supplies the *proof-producing* pattern (build the term, let the kernel
  re-check) and the *attribute-tagged rule database* template (scoped
  env-extension + `add` callback + `getState` reader) that a future
  discrimination-tree registry would follow.
