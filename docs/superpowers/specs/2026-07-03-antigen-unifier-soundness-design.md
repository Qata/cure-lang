# Antigen V2 — Unifier Soundness — Design

**Status:** design (Stage 0, autopilot Phase 3) · **Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b`
**Umbrella:** `2026-07-03-antigen-untrusted-machinery-design.md` §V2 · **Predecessors:** V3 (elab soundness), V1 (normalizer soundness)

## 1. Goal

Extend Antigen to the two **untrusted** unification engines, per the operator's
locked scope (umbrella open-item #4): **both** `Cure.Elab.Unify` (Core terms with
metavariables — feeds elaboration) and `Cure.Types.Unify` (surface types — solves
implicit arguments). A unifier that reports `{:ok, …}` with a substitution that
does **not** actually make the two sides equal is a soundness hole: the elaborator
trusts the solution, assembles a core term around it, and — while the kernel
*re-checks* the assembled term (so a wrong solve is often caught downstream) — the
unifier is exactly the kind of untrusted machinery this initiative exists to
pin independently.

The two engines are one vertical but have **different oracle situations**, which
drives a two-family split:

- **V2a — `Elab.Unify`** operates on Core terms and the trusted `Cure.Core.Conv`
  is a genuine external oracle for "do these two terms unify." → a real
  **differential**.
- **V2b — `Types.Unify`** operates on surface types and has **no** trusted
  external equality (it accepts non-syntactic matches: `:any` widening,
  `int`/`float` widening, refinement-stripping, named/record/adt matching). No
  kernel oracle applies. → **intrinsic algebraic laws + a fixpoint
  self-consistency** check (the same oracle-free tactic V1c used on the
  untranslatable fragment).

## 2. Targets (verified against source)

### `Cure.Elab.Unify` (`lib/cure/elab/unify.ex`)

- `unify(t1, t2, ctx, sig \\ nil) :: {:ok, MetaCtx.t()} | {:error, term()}` —
  first-order unification of Core terms bearing metavariables `{:meta, id}`,
  refining `ctx`. With `sig` (a `Cure.Core.Env`), closed meta-free syntactic
  failures fall back to δ-capable `Conv` (a documented *completeness* improvement
  that itself rests on `Conv`).
- `zonk(t, ctx) :: uterm()` — finalises a term by substituting every solution away.
- `Cure.Elab.MetaCtx`: `new/0`, `fresh/1 :: {t, id}`, `solution/2`, `solved?/2`.
- Metavariables live only in the elaborator; a term reaching the kernel must be
  fully zonked. Error tags observed: `{:cannot_unify,…}`, `{:arity_mismatch,…}`,
  `{:occurs_check, id, t}`, `{:escaping_variable, id}`.

### `Cure.Types.Unify` (`lib/cure/types/unify.ex`)

- `unify(t1, t2) :: {:ok, subst, trace} | {:error, reason, trace}`; `unify/3`
  (starting subst); `unify_many/1`. `subst :: %{String.t() => type}`.
- `apply_subst(type, subst) :: type` — substitutes solved vars through a type.
- Flex variables are `{:type_var, name}` (string `name`), occurs-checked in `bind`.
- **Non-syntactic accepts** (these are why no external structural oracle exists):
  `do_unify(t, t) → reflex`; `{:refinement, base, _, _}` stripped on either side;
  `:any` matches anything; `{:int, :float} → widening`; `{:named, a}` matches a
  `{:record, key, …}`/`{:adt, key, …}` when `downcase(a) == to_string(key)`.

## 3. Properties

### V2a — `Elab.Unify` (differential, oracle = `Conv`)

- **`unify/soundness` (the master property):** if
  `unify(t1, t2, ctx, sig) = {:ok, ctx')`, then `zonk(t1, ctx')` and
  `zonk(t2, ctx')` are `Conv`-convertible:
  `Conv.conv?(zonk(t1,ctx'), zonk(t2,ctx'), [], 0, sig) == true`. A `{:ok, …}`
  whose zonked sides are **not** convertible is `{:violation, {:unify_unsound,…}}`.
  This is the honest soundness question the δ-fallback's moduledoc waves at
  ("a wrong accept here is caught downstream") — V2a checks it *here*.
- **`unify/intrinsic` (no oracle):**
  - *occurs-check:* no returned solution is cyclic — for every solved `?id`,
    `id` does not occur in `force`-resolved `solution(ctx', id)`.
  - *idempotent zonk:* `zonk(zonk(t, ctx'), ctx') == zonk(t, ctx')`.
  - *well-scoped / meta-closed:* if `unify` succeeded on meta-free inputs, the
    zonked sides are meta-free (no `{:meta,_}` survives — the `escapes?`/
    `strengthen` scope machinery held).

### V2b — `Types.Unify` (intrinsic + fixpoint, no external oracle)

- **`unify_types/fixpoint` (self-consistency, the soundness proxy):** if
  `unify(t1, t2) = {:ok, s, _}`, then re-unifying the substituted sides needs no
  new work: `unify(apply_subst(t1, s), apply_subst(t2, s), s) = {:ok, s', _}` with
  `s' == s`. A solution that does not actually resolve its own constraint (new
  bindings appear, or the re-unification fails) is `{:violation, {:solution_unstable,…}}`.
- **`unify_types/intrinsic` (no oracle):**
  - *occurs-check:* a cyclic constraint (`{:type_var,"a"}` vs `{:list,{:type_var,"a"}}`)
    yields `{:error, …}`, never `{:ok, …}`.
  - *idempotent substitution:* `apply_subst(apply_subst(t, s), s) == apply_subst(t, s)`.
  - *solved-var elimination:* `apply_subst(t, s)` contains no `{:type_var, n}` for
    any `n ∈ Map.keys(s)`.

## 4. Assay & injectable seam

New module `Antigen.Assays.Unifier` with `run/1` → `run/2` (op-map seam), mirroring
`Antigen.Assays.{Elab,Normalizer}`. `@assay_fuel 500_000` wraps every `Conv` call
in `Cure.Core.Normalise.with_fuel/2` (defensive; these terms are first-order and
terminating). Four assay ids:

| id | engine | property | oracle |
|---|---|---|---|
| `unify/soundness` | `Elab.Unify` | zonked sides `Conv`-equal | `Conv` |
| `unify/intrinsic` | `Elab.Unify` | occurs / idempotent-zonk / meta-closed | none |
| `unify_types/fixpoint` | `Types.Unify` | re-unify substituted = no new bindings | none |
| `unify_types/intrinsic` | `Types.Unify` | occurs / idempotent-apply / var-elim | none |

**Op-map** (`@real`), injecting the **code-under-test** at the assay boundary (the
Run C sensitivity pattern; oracle ops stay real):

```elixir
%{
  # Elab.Unify (V2a)
  eu_unify: &Cure.Elab.Unify.unify/4,
  eu_zonk:  &Cure.Elab.Unify.zonk/2,
  eu_solution: &Cure.Elab.MetaCtx.solution/2,
  conv:     &Cure.Core.Conv.conv?/5,       # trusted oracle
  # Types.Unify (V2b)
  tu_unify: &Cure.Types.Unify.unify/3,
  tu_apply: &Cure.Types.Unify.apply_subst/2
}
```

Negative controls inject a broken code-under-test op and prove each assay is
load-bearing:
- `unify/soundness`: an `eu_unify` stub returning `{:ok, ctx}` **unchanged** on a
  problem whose sides only unify *after* a solve → zonked sides not `Conv`-equal →
  caught.
- `unify/intrinsic`: an `eu_solution` stub returning a **cyclic** term for a solved
  id → occurs violation.
- `unify_types/fixpoint`: a `tu_unify` stub returning `{:ok, s, []}` with a subst
  that leaves the constraint unsatisfied → re-unification produces a new binding /
  error → `{:solution_unstable,…}`.
- `unify_types/intrinsic`: a `tu_unify` stub accepting a cyclic constraint → occurs
  violation; a `tu_apply` stub that leaves a solved var in place → var-elim
  violation.

## 5. Generator

New module `Antigen.Generators.UnifyProblem` producing **fixed catalogs** (the
elab/normalizer reconciliation — no corpus/Coverage surgery; a new lightweight
`:unify_problem` challenge kind, typespec-only, wired via `assay_module/1` and a
dedicated test):

- `elab_soundness_challenges/0` / `elab_intrinsic_challenges/0` — payload
  `%{t1, t2, ctx, sig}` over Core terms. Catalog covers: a bare metavar solve
  (`{:meta,0}` vs `{:ctor, :S, [{:global, :z}]}`), a structural ctor/data match
  driving nested solves, a binder case (`{:pi, d, {:meta,0}}` vs `{:pi, d, c}`),
  and a no-metavar reflexive pair. `ctx` seeded via `MetaCtx.new/0` +`fresh/1`;
  `sig` is `nil` for the syntactic cases (a δ-fallback case may pass a small env).
- `types_challenges/0` — payload `%{t1, t2}` over surface types. Catalog covers:
  `{:type_var,"T"}` vs `:int`; `{:list,{:type_var,"T"}}` vs `{:list, :int}`;
  `{:tuple,[{:type_var,"A"},{:type_var,"B"}]}` vs `{:tuple,[:int,:string]}`; a
  refinement-stripped case; an `:any`-widening case; and (for the occurs control)
  a hand-built cyclic pair used only in the negative test, never the clean catalog.

## 6. Invariants (what must never regress)

- No `Cure.Core.*`, `Cure.Elab.*`, or `Cure.Types.*` edits — both engines reached
  read-only through the op-map. No `:meck`, no new dependency.
- `Antigen.Assays.Unifier` contains no literal `StreamData` token (the
  `architecture_test` grep — a lesson banked from V1's Stage-5 trip; keep the word
  out of moduledoc/comments too).
- Assay `run/1,2` returns only `:ok | {:violation, term()}` (matches the `@spec`
  and both `Runner.replay_one/1` and `Runner.explore/1`'s no-catch-all dispatch —
  no third outcome kind). Incompleteness/reach-gaps are out of scope here (a
  `Conv`-equal pair `Elab.Unify` rejects is not a soundness violation).
- The whole clean catalog re-checks `:ok` under the real ops (a real infection
  ⟹ STOP and report; do not weaken a test).

## 7. Non-goals

- No fixes to either unifier (V2 *finds*; a surfaced infection is reported, not
  patched, without separate authorization).
- No higher-order / Miller-pattern unification coverage (a documented `Elab.Unify`
  extension point; out of first-order scope).
- No random unify-problem fuzzer — a curated fixed catalog (elab pattern). A
  generator-expansion follow-on could widen coverage.
- No surface-type external oracle invented for `Types.Unify` — V2b stays intrinsic
  + fixpoint by design (§1).
- No SMT (that is V6).

## 8. Open items (for the plan / review to pin)

1. **`Conv.conv?` arg shape for zonked Core terms** — confirm `conv?(z1, z2, [],
   0, sig)` is the right call for closed first-order terms (the `Elab.Unify`
   δ-fallback itself calls exactly `Conv.conv?(z1, z2, [], 0, sig)`, so this is
   grounded — the plan should cite that call site).
2. **`MetaCtx` construction in the generator** — the catalog must allocate metas
   via `fresh/1` so ids line up with the terms that mention them; the plan pins
   the exact `{ctx, id}` threading for each multi-meta entry.
3. **`tu_unify` arity** — `Types.Unify.unify/3` (with starting subst `%{}`) is the
   seam so a negative control can inject a starting subst; the fixpoint property
   re-invokes with `s`. Confirm `unify/2` vs `unify/3` default at the call site.
4. **Fixpoint equality of substitutions** — `s' == s` is a plain map compare;
   confirm `apply_subst` produces canonical terms so no spurious inequality
   (e.g. no ordering/whitespace artifacts — maps compare by content, so fine).
5. **Meta-closed check for V2a** — "zonked sides meta-free" uses a local
   `meta_free?/1` in the assay (the engine's is private); the plan supplies it,
   independent of `Elab.Unify`'s copy.

## 9. Test catalog (for the plan — §5 of the plan will expand each)

1. V2a soundness baseline (`?0` vs `S z`) → `:ok`.
2. V2a soundness structural (nested ctor solve) → `:ok`.
3. V2a soundness negative control (identity `eu_unify` stub) → `{:unify_unsound,…}`.
4. V2a intrinsic baseline (occurs + idempotent zonk + meta-closed) → `:ok`.
5. V2a intrinsic occurs negative control (cyclic `eu_solution`) → `{:occurs,…}`.
6. V2b fixpoint baseline (`T` vs `int`; `list(T)` vs `list(int)`) → `:ok`.
7. V2b fixpoint negative control (unstable `tu_unify` stub) → `{:solution_unstable,…}`.
8. V2b intrinsic baseline (occurs rejects cyclic; idempotent apply; var-elim) → `:ok`.
9. V2b intrinsic var-elim negative control (leaky `tu_apply` stub) → `{:var_not_eliminated,…}`.
10. Generator+wiring: each catalog non-empty & correctly tagged; `Runner.replay_one/1`
    dispatches every `unify*/…` id and the whole clean catalog is `:ok`.

## 10. Next (umbrella roadmap)

After V2: V5 totality-closure, V4 erasure/relevance, V6 SMT lint. **No auto-merge.**
