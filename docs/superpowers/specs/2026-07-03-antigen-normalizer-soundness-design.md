# Antigen V1 — Normalizer Soundness (Phase 2) Design

**Status:** proceeding under the operator's roadmap resolution (V1 is Phase 2, and
open-question #2 resolved *include the intrinsic-law-only assay over the
untranslatable fragment*). Second phase of the untrusted-machinery initiative
([umbrella spec](2026-07-03-antigen-untrusted-machinery-design.md), task #66),
after V3 (elaborator soundness). Autonomous continuation via the `/loop` session —
the operator merges `autopilot/antigen-tier-b` and can course-correct before then.

## 1. Problem

`Cure.Types.Reduce` is the **untrusted** type-level normalizer the type checker
uses for definitional equality — e.g. deciding `Vector(T, 3 + 5) ≡ Vector(T, 8)`
at a call site without an SMT call. Its public surface:

- `normalize(ast, bindings) :: ast` — `do_substitute(ast, bindings)` (surface
  variable substitution) then `kernel_normalize/1`.
- `equal?(a, b, bindings) :: boolean` — `normalize(a) == normalize(b)`. **This is
  the front-door soundness consumer:** the type checker treats a `true` here as
  "these two types are definitionally equal" and accepts the program. A *false
  positive* (`equal?` returns `true` for two genuinely-unequal types) is a real
  unsoundness — it admits an ill-typed program — with no kernel backstop, exactly
  like an SMT false discharge.

The arithmetic itself is **not** the untrusted part: `kernel_normalize/1` calls
`CoreBridge.to_core(ast)` and, when it succeeds, delegates the whole reduction to
the **trusted kernel** (`Eval.eval([])` → `Quote.reify()`), reading the result
back with `CoreBridge.from_core/1`. When `to_core` returns `:error` (an
untranslatable former — named ref, refinement, n-ary tuple), it falls to
`structural_congruence/1`, which recurses into children through the kernel again.

So the untrusted surface under test is precisely: **(a) `do_substitute` (surface
substitution), (b) the `CoreBridge` translation round-trip
(`to_core`/`from_core`), and (c) `structural_congruence` (the untranslatable-
fragment fallback).** A bug in any of these can make `normalize`/`equal?` return a
wrong normal form even though the kernel's arithmetic is correct — a
translation/substitution/congruence bug, not an arithmetic bug.

## 2. The oracle and the three assay families

The trusted `Cure.Core` normalizer (`Eval.eval` / `Quote.reify` / `Conv`) is the
differential oracle for the **translatable** fragment. The **untranslatable**
fragment has no oracle, so it is pinned by intrinsic algebraic laws the module's
own contract guarantees.

### V1a — Differential `normalize` (translatable fragment)

**Property.** For a type-level `ast` that `CoreBridge.to_core` accepts, the
surface normal form must agree with an *independent* trusted-kernel
normalization of the same term:

> `CoreBridge.to_core(Types.Reduce.normalize(ast, %{}))` and
> `Eval.eval(to_core(ast), []) |> Quote.reify()` are `Conv`-equal core terms.

Both routes normalize the same starting term; V1a checks the untrusted bridge
round-trip + surface plumbing did not corrupt the result the kernel would give.
An infection is a surface normal form that translates to a core term the kernel
says is *not* convertible to the kernel's own normal form of the input —
`{:normalize_disagrees_with_kernel, ast, …}`.

### V1b — Differential `equal?` (translatable fragment) — the soundness property

**Property (the load-bearing one).** For translatable `a`, `b`:

> `Types.Reduce.equal?(a, b, %{})` ⟺ the trusted kernel finds
> `to_core(a)` and `to_core(b)` convertible (`Conv.conv?` on their evaluated
> values).

The **`true`-side is the soundness direction**: `equal?` returning `true` while
the kernel says *not convertible* is an unsound definitional-equality discharge →
`{:equal_unsound, a, b}` (admits an ill-typed program). The `false`-side is
*completeness* (a surface `equal?` returning `false` where the kernel says
convertible is an incompleteness/reach gap, surfaced but a weaker signal). Both
are reported, tagged distinctly; only the unsound `true` is a hard infection.

### V1c — Intrinsic laws (untranslatable fragment, no oracle)

For `ast` where `CoreBridge.to_core(ast) == :error` (so `structural_congruence`
governs), the module's own moduledoc guarantees two laws that need no oracle:

- **Idempotence:** `normalize(normalize(ast, b), b) == normalize(ast, b)` — a
  normal form is a fixpoint. A second pass that changes the term is a
  non-confluent / non-terminating congruence bug → `{:not_idempotent, ast, …}`.
- **Monotone non-increase:** the moduledoc states "the result is *always*
  syntactically smaller-or-equal to the input," so
  `term_size(normalize(ast, b)) <= term_size(ast)`. A congruence step that grows
  the term violates the stated contract → `{:size_increased, ast, …}`.

These make the untranslatable fragment (which V1a/V1b cannot reach — no core
translation exists) non-vacuously covered, per the operator's open-Q2 resolution.

## 3. Generators

A new `Antigen.Generators.SurfaceExpr` producing type-level surface ASTs (the
`{tag, meta, children}` grammar `Types.Reduce` consumes), in two labelled
streams so the assay knows which family applies:

- **`:translatable`** — arithmetic/boolean/comparison expressions over integer &
  boolean literals and bound variables (with a `bindings` map), all inside the
  fragment `CoreBridge.to_core` accepts. Feeds V1a + V1b. For V1b, pairs are
  generated both as *kernel-equal* (e.g. `3 + 5` vs `8`, must be `equal? = true`)
  and *kernel-unequal* (e.g. `3 + 5` vs `9`, must be `equal? = false`) so the
  soundness direction is exercised on real should-be-true and should-be-false
  inputs.
- **`:untranslatable`** — expressions headed by a former `to_core` rejects
  (named type ref, refinement `{n | p}`, n-ary tuple) wrapping translatable
  sub-terms, so `structural_congruence` runs and V1c's laws are non-trivial.

The generator lives under `lib/antigen/generators/` (StreamData-permitted glob).
Wiring mirrors the existing families: an assay-id → module entry in the runner's
`assay_module/1`, and generator entries in `default_gen` (weight 1 each) so
`mix antigen` exercises V1 — unless grounding shows the surface grammar is better
run as a fixed catalog (like elab), in which case the plan reconciles to that.

## 4. Assay module

`Antigen.Assays.Normalizer`, assay ids `normalizer/differential`,
`normalizer/equal`, `normalizer/intrinsic`. Each `run/1` delegates to a `run/2`
with an injectable oracle-op map (`%{to_core, from_core, eval, reify, conv,
normalize, equal}`) — the Run C / V3 seam pattern — so a negative control can
inject a broken bridge/reducer without touching `Cure.Types.*` or `Cure.Core.*`
and without `:meck`. Every kernel normalization runs under the committed
`@assay_fuel` 500_000 floor; `:fuel_exhausted` is its own reported outcome.

## 5. Testing strategy (behavioral, immutable; strict TDD)

New `test/antigen/assays/normalizer_test.exs`:

1. **V1a baseline.** `normalize(3 + 5)` agrees with the kernel normal form of
   `3 + 5` → `:ok`.
2. **V1a negative control.** Via `run/2`, inject a `from_core` that corrupts the
   read-back (returns a wrong literal) → `{:normalize_disagrees_with_kernel, …}`.
   Proves V1a is load-bearing.
3. **V1b soundness baseline.** `equal?(3 + 5, 8) == true` and the kernel agrees →
   `:ok`; `equal?(3 + 5, 9) == false` and the kernel agrees → `:ok`.
4. **V1b negative control.** Inject a reducer stub whose `equal?` returns `true`
   for a kernel-unequal pair → `{:equal_unsound, …}`. The load-bearing proof.
5. **V1c idempotence.** An untranslatable-headed term: `normalize` is a fixpoint
   → `:ok`; a stubbed congruence that mutates on the second pass →
   `{:not_idempotent, …}`.
6. **V1c monotone size.** `normalize` output is size-≤ input → `:ok`; a stubbed
   congruence that grows the term → `{:size_increased, …}`.
7. **Determinism / regression.** `run/2` with the real op-map is byte-identical
   to `run/1`; existing `Types.Reduce` tests untouched.
8. **Runner wiring.** The three `normalizer/*` ids resolve through
   `assay_module/1`; a generated challenge flows through `explore/1`.

## 6. Invariants

- **Read-only TCB + read-only `Cure.Types`.** V1 tests the untrusted normalizer
  against the trusted kernel; neither is edited. The oracle is reached only
  through the assay's `@real` op-map.
- **Deterministic, banked, replayable.** Fixed fuel floor (500_000); no RNG/clock
  in the assay; the generator's StreamData seeds are corpus-banked like every
  other family.
- **StreamData quarantine.** Assay under `lib/antigen/assays/` (no `StreamData`
  literal); generator under `lib/antigen/generators/` (StreamData allowed).
- **No new dependency, no `:meck`.** The `run/2` op-map is the only injection path.
- **Known-label + negative controls.** Translatable pairs carry their
  should-be-equal/unequal label; V1c terms carry `:untranslatable`. Tests
  #2/#4/#5/#6 are the load-bearing negative controls.

## 7. Open items (for the plan / review to pin)

1. **`CoreBridge.to_core`/`from_core` exact signatures + the translatable grammar
   boundary** — the plan reads `lib/cure/types/core_bridge.ex` and pins which
   `{tag, meta, children}` heads translate, so the generator's `:translatable` and
   `:untranslatable` streams are provably on the right side of `to_core`.
2. **`Conv` entry for surface-derived core** — V1a/V1b compare core terms/values;
   the plan pins whether to compare via `Conv.conv?` on values or `Conv.conv_values?`,
   and the `depth`/`sig` args (empty context, seeded env), mirroring V3.
3. **`term_size` for surface ASTs** — a simple node count over the
   `{tag, meta, children}` grammar (meta excluded); pin in the plan.
4. **Generator wiring: `default_gen` vs fixed catalog** — decide from grounding
   whether `SurfaceExpr` is a StreamData generator in `default_gen` or a curated
   catalog like `elab_complete`; the plan reconciles.

## 8. Non-goals (Phase 2)

- No V2 (unifier), V4/V5/V6 — later phases.
- No `Types.Reduce` *fix*: V1 finds unsound/incorrect normalization; fixing any
  infection it banks is separate follow-up.
- No SMT (that is V6); V1 is the *pre-SMT* definitional-equality layer only.
- No new kernel/`Cure.Types` capability — read-only differential + intrinsic laws.
