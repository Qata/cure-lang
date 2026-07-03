# Antigen Tier-B Reach Expansion — Design

**Status:** design (Stage 0, autopilot) · **Date:** 2026-07-04 · **Branch:** `autopilot/antigen-tier-b`
**Builds on:** `2026-07-02-antigen-tier-b-term-generator-design.md` (+ its report's "Reach left open")
**Predecessor initiative:** untrusted-machinery (V1–V6, complete; both findings fixed 2026-07-04)

## 1. Goal

Widen the reach of the **existing** dependent Core term generator
(`Antigen.Generators.Term`, mode-directed bidirectional inversion) and add two new
assays that consume the richer stream. Operator-selected scope: **all three** of the
Tier-B report's "reach left open" items that concern the generator itself —

1. **Richer generator menu** — Π/Σ goal seeds + a parametric (type-parameter) family.
2. **`erasure_preservation` assay** — erasure preserves computation, on the generated stream.
3. **Ill-typed mutation for the new type formers** — extend `mutation/rejection` with
   operators that break the Π/Σ/parametric terms Phase 1 unlocks.

One initiative, **three sequentially-committed phases**. Phase 1 is first because the
richer stream is what Phases 2 and 3 consume — they are strictly deeper with it in place.

## 2. Current state (verified against source)

- **`Antigen.Generators.Term`** (`term.ex`): `gen_term(ctx, goal) = Gen.sized(...)`,
  `@max_size 12`, `@gen_fuel 500`; lazy `gen/3`; `intro_rules/4` already dispatches on
  `{:pi,_,_}`, `{:sigma,_,_}`, `{:data,:Vec,_,_}`, `{:data,:Nat,_,_}`, `{:data,:Bd,_,_}`,
  `{:type,_}`. Produces `:typed_term` challenges tagged for the three assay ids.
- **`SigMenu`** (`sig_menu.ex`): `goal_types = [nat(), bd(), vec(z()), vec(s(z()))]` — the
  **top-level goal seeds are only closed data types** (no Π/Σ, no type parameters).
  `canon/2`, `inhabitable?/2` already cover `:pi`/`:sigma` (they arise only as *sub-goals*
  today). `env_of(:v1)` holds the fixed signature (Nat, Bd, Vec, plus/dbl defs).
- **`Antigen.Assays.Term`** (`term.ex`): op-map seam `@real_kernel %{infer: &Kernel.infer/2,
  check: &Kernel.check/3}`, `run/1`→`run/2`, dispatch on assay id
  (`term/infer_check`, `term/subject_reduction`, `term/normalization`); payload `p` has
  `.term`, `.type`, `.ctx`. Uses `Normalise.quote`, `Conv`, `Serialize`.
- **Mutation** already exists and **already consumes `Term.gen_term`**: generator
  `Mutation.build(ctx, op)` with `op ∈ {head_swap, ctor_arg, index_mismatch, app_domain,
  out_of_scope_var, proj_non_pair}`; assay `mutation/rejection` — ill-typed `:mutant_term`
  MUST be rejected by `Kernel.infer` (`{:error,_}`→`:ok`; `{:ok,_}`→antibody).
- **Erasure** (`Cure.Elab.Erase.erase/2`) — just made idempotent (2026-07-04); erased terms
  are non-dependent runtime forms (validated by `Term.term?`, NOT kernel typing — a locked
  V4 fact). **`Eval.eval/2`** maps a Core term + env to a value (`:vctor`/`:vlam`/`:vpair`/…).

## 3. Phase 1 — Richer generator menu

**Files:** `lib/antigen/generators/sig_menu.ex` (+ possibly `term.ex` for new intro/elim
coverage). Antigen-only; no kernel edits.

- **Π and Σ goal seeds.** Add closed, inhabitable function/pair goal types to
  `goal_types/0` — e.g. `{:pi, nat(), nat()}` (`Nat→Nat`), `{:pi, nat(), bd()}`,
  `{:sigma, nat(), vec(<idx>)}` (`Σ Nat. Vec`). The `intro_rules` for `:pi`/`:sigma`
  already fire, so top-level goals now produce λ-abstractions and pairs. Confirm
  `inhabitable?/2` returns true for each new seed in the empty context (it already
  recurses through `:pi`/`:sigma`) so `canon/2` gives a total fallback.
- **Parametric (type-parameter) family.** Add ONE parametric family to `env_of(:v1)` that
  exercises the `params` slot of `{:data, name, params, indices}` — a `List(A)` (param `A`,
  no index) is the minimal clean choice: ctors `Nil : List(A)`, `Cons : A -> List(A) ->
  List(A)`. Add its goal seed(s) (`List(Nat)`, `List(Bd)`), `intro_rules` for
  `{:data, :List, [A], []}` (choose `Nil`/`Cons`, recursing on `A` and `List(A)`),
  `canon` (`Nil`), and `inhabitable?`. (Exact eliminator support is an open item — §8-1.)
- **Health gate.** The existing static-health meta-tests (discard-rate, binder-usage,
  reduction-activity) must stay green — a richer menu must not tank the well-typed-not-
  useless ratios. This is the acceptance gate for Phase 1, alongside the three differential
  assays continuing to pass (now over deeper terms).

**Effect:** no new assay — Phase 1 automatically deepens `term/infer_check`,
`term/subject_reduction`, `term/normalization` by feeding them λ/pair/list terms.

## 4. Phase 2 — `erasure_preservation` assay

**Files:** `lib/antigen/assays/term.ex` (new dispatch clause) or a new
`lib/antigen/assays/erasure_preservation.ex`; `term.ex` generator (`@assay_ids` +1);
`runner.ex` (one dispatch clause). Consumes the same `:typed_term` stream.

**Property (to pin precisely in review — §8-2).** For a generated well-typed `t : T`:
erasure preserves the computational result. Candidate formulations, strongest-first:
- **(a) Commutation:** `nf(erase(t)) ≡ erase(nf(t))` structurally — erasure commutes with
  normalization. Strong and oracle-free (both sides are Core terms; compare via `Serialize`
  or structural `==`). Preferred **if** it holds for the kernel's erase/nf semantics.
- **(b) Value-totality + well-formedness:** `Term.term?(erase(t))` is true AND
  `Eval.eval(erase(t), env)` produces a value without raising. Weaker but unconditionally
  tractable; catches an erase that yields an ill-formed or non-evaluable term (exactly the
  pre-fix drop-a-present-arg failure mode).

The assay returns `:ok | {:violation, {:erasure_not_preserved, detail}}`. Wire via the
op-map seam (`erase`, plus `infer` to gate on well-typedness).

**Negative control (must infect).** Inject a broken erase into the op-map — e.g. the
pre-fix zip-realignment behavior, or a stub dropping a `:present` arg — and confirm the
assay reports `{:violation, {:erasure_not_preserved, _}}` on a term where the real erase
passes. (This is what makes the assay load-bearing; V2's dead-branch lesson.)

## 5. Phase 3 — Ill-typed mutation for the new type formers

**Files:** `lib/antigen/generators/mutation.ex` (+ new operators), `challenge.ex`
(`@known_atoms` for any new op kinds), tests. Reuses the existing `mutation/rejection`
assay unchanged (it already asserts kernel rejection of `:mutant_term`).

New mutation operators targeting Phase 1's type formers (each builds a
construction-guaranteed ill-typed term the kernel must reject):
- **`pair_component`** — in a Σ-typed pair, replace one component with a well-typed term of
  the wrong type (breaks the Σ's dependent second component or first-component type).
- **`lam_body_type`** / **`app_result`** — for a Π-typed λ or its application, supply a
  body/argument that violates the codomain/domain (distinct from the existing `app_domain`,
  which targets first-order data application — this targets the new function-typed stream).
- **`type_param_mismatch`** — for a parametric `List(A)` term, `Cons` an element of the
  wrong parameter type (`Cons (b : Bd) : List(Nat)`), which the kernel must reject.

Each new operator gets a test asserting the produced mutant is rejected by `Kernel.infer`
(the `mutation/rejection` `:ok`), and — the load-bearing check — that WITHOUT the mutation
the analogous well-typed term is *accepted* (so the operator genuinely introduces
ill-typedness, not a term that was already rejected for another reason).

## 6. Invariants (what must never regress)

- **No kernel/TCB edits.** `Cure.Core.*`/`Cure.Elab.*` reached read-only through op-maps.
  Phase 1's menu additions and Phase 3's operators live entirely in `Antigen.*`.
- **StreamData quarantine.** Nothing under `Antigen.Generators.*`/`Antigen.Assays.*` may
  contain the literal `StreamData` token (arch test). New generator code uses the `Gen` DSL.
- **Assays return only `:ok | {:violation, term()}`** (non-normalization stays a distinct
  tagged violation, never conflated).
- **Health gate holds** after Phase 1 (discard-rate/binder-usage/reduction-activity).
- **The full existing suite stays green** each phase (2732 baseline); each new assay/operator
  ships with a negative control that demonstrably infects.
- New `Challenge` payload shapes/atoms interned in `Challenge.@known_atoms` if banked.

## 7. Non-goals

- **No `Backend.ChoiceSeq`** (the Hypothesis-style shrinking backend) — a separate reach
  item, its own initiative.
- **No `conversion_termination` assay** — the other listed reach item; deferred.
- No new kernel *features* (e.g. we add a `List` family to the Antigen *menu env*, not to
  the language's stdlib).
- No unbounded generator growth — `@max_size`/`@gen_fuel` stay the committed budgets; the
  richer menu adds breadth (more goal shapes), not depth blow-up.
- Not a fuzzer rewrite — the generator stays the reified-`Gen` inversion generator.

## 8. Open items (for the plan / spec-review to pin)

1. **`List(A)` eliminator support.** Phase 1's parametric family needs `intro_rules`
   (Nil/Cons) at minimum. Whether to also generate a `List` *eliminator* (recursor/case)
   — which the differential trio would exercise for reduction — depends on how the existing
   `gen` handles `:case`/eliminators for data families (Vec already has some — confirm the
   pattern and reuse it; if eliminator generation is heavy, ship intro-only in Phase 1 and
   note elim as a follow-up).
2. **Exact `erasure_preservation` property.** Validate (a) commutation `nf∘erase ≡ erase∘nf`
   against the kernel's actual erase/normalize semantics (does erasing under a binder then
   normalizing agree with normalizing then erasing, given erased args are dropped?). If (a)
   does not hold universally, ship (b) value-totality+well-formedness as the committed
   property and record why (a) was rejected. Confirm the `Eval.eval` env for an erased term
   (erased terms have no dependent context — the empty/rebuilt env).
3. **`inhabitable?` for Π/Σ/List seeds in the empty context.** Confirm each new `goal_types`
   seed is actually inhabitable so `canon/2` never fails (a non-inhabitable seed would make
   the size-0 fallback raise). Π into an inhabitable codomain and Σ of inhabitables are fine;
   confirm the chosen index terms for any `Vec` inside a Σ seed.
4. **Mutation `@known_atoms` + payload.** New operators may introduce new atom tags
   (`:pair_component`, `:type_param_mismatch`, …) — intern them if mutants are banked to the
   corpus; confirm whether `mutation/rejection` banks (it does bank antibodies).
5. **Menu-version bump.** `SigMenu.env_of(:v1)` is versioned — decide whether the parametric
   family extends `:v1` or introduces `:v2` (and whether existing banked `:v1` seeds still
   replay). Prefer extending `:v1` additively if it doesn't invalidate banked seeds.

## 9. Test strategy (per phase, red-green)

- **Phase 1:** red — a test asserting `SigMenu.goal_types` includes a Π/Σ/List seed and that
  `Term.gen_term` over a Π goal produces a `:lam` (and over `List(Nat)` a `:ctor :Cons/:Nil`)
  fails today; green after the menu additions. Health-gate meta-tests + the three differential
  assays stay green over the richer stream.
- **Phase 2:** red — the `erasure_preservation` assay clause doesn't exist (dispatch raises);
  green after implementing it; the negative control (broken erase) infects.
- **Phase 3:** red — each new mutation operator (`build(ctx, :pair_component)` …) is undefined;
  green after adding it; `mutation/rejection` returns `:ok` on the mutant AND the un-mutated
  analog is accepted (the operator genuinely ill-types).
- **Each phase:** full suite green before moving on (one build at a time).

## 10. Next (roadmap)

Remaining Tier-B reach items after this initiative: `Backend.ChoiceSeq`,
`conversion_termination`, and A10's broader wiring of the known-label verticals onto the
generated stream. **No auto-merge.**
