# Antigen V4 — Erasure & Relevance Soundness — Design

**Status:** design (Stage 0, autopilot Phase 5) · **Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b`
**Umbrella:** `2026-07-03-antigen-untrusted-machinery-design.md` §V4 · **Predecessors:** V3 (elab), V1 (normalizer), V2 (unifier), V5 (totality-closure)

## 1. Goal

Extend Antigen to the **untrusted erasure & relevance machinery**: the `{0,ω}`
erasure that strips computationally-irrelevant (quantity-0 / `:erased`) sub-terms
before emission (`Cure.Elab.Erase`), and the relevance checker that guarantees no
`:erased` binder is used relevantly (`Cure.Elab.Relevance`). These implement the
**LOCKED** erasure relevance-check decision (memory `erasure-relevance-check-decision`):
the `{0,ω}` check enforces the spec-§2 "computationally-relevant" rule — reject
return / present-arg / scrutinise / apply of an erased binder; make params present;
do **not** auto-promote (preserving the zero-footprint guarantee). Erasure soundness
matters two ways: dropping a **relevant** (present) sub-term loses runtime data (a
wrong program), and **keeping** an erased sub-term breaks the zero-footprint
guarantee the whole `{0,ω}` design rests on.

**What is already covered vs. what is new.** The existing
`Antigen.Generators.ElabErasure` produces **surface-program** challenges
(`kind: :elab_program`, `assay: "elab/erasure"`) that test the relevance rule
*end-to-end through elaboration* (accept/reject whole programs). V4 targets the
**Core-level** functions those depend on, with no elaboration confound:

- `Cure.Elab.Erase.erase/2` — the Core→runtime term stripper (zero existing
  direct coverage).
- `Cure.Elab.Relevance.check/4` — the relevance decision, tested **directly** on
  Core bodies with known relevant-use sites (complements, does not duplicate, the
  surface-program `elab/erasure` assay).

## 2. Targets (verified against source)

### `Cure.Elab.Erase` (`lib/cure/elab/erase.ex`)

- `erase(env, term) :: term` — recursively drops `:erased` constructor arguments
  (`{:ctor, c, args}` keeps only positions where `Inductive.ctor_quantities(env, c)`
  is `:present`; `nil` quantities ⇒ all `:present`), drops `:erased` application
  arguments for a `{:global, name}` head (via the def's `quantities`, padding
  extra args as `:present`), and structurally recurses through
  `:lam/:app/:pair/:fst/:snd/:pi/:sigma/:data/:case`. Non-computational forms
  collapse: `{:refl, _} → {:ctor, :cure_refl, []}`, `{:eq, …} → {:ctor, :cure_eq, []}`,
  `{:rewrite, _p, _m, body} → erase(body)`. `erase(_env, term) → term` (leaves).
- `has_hole?(term) :: boolean` — structural hole detector over the full taxonomy.

### `Cure.Elab.Relevance` (`lib/cure/elab/relevance.ex`)

- `check(env, name, quantities, body) :: :ok | {:error, {:erased_used_relevantly,
  %{def: atom(), binder: non_neg_integer(), site: site()}}}` where
  `site :: :returned | :present_arg | :scrutinee | :applied`. Non-list `quantities`
  ⇒ `:ok` (vacuous). Walks `body` tracking de Bruijn depth; an `:erased` binder
  used at any of the four relevant sites is the violation. Erased argument
  positions are exempt (an erased binder may appear in another erased position).

### `Cure.Core.Inductive.ctor_quantities(env, cname) :: [:present | :erased] | nil`

The quantity vector `Erase`/`Relevance` both consult — the shared oracle for
"which positions are erased."

## 3. Properties (two families)

### V4a — `Erase.erase/2` (intrinsic + differential)

- **Idempotence:** `erase(env, erase(env, t)) == erase(env, t)` — erasure is a
  normal form; re-erasing changes nothing. A non-idempotent erasure is
  `{:violation, {:erase_not_idempotent, t}}`.
- **Hole preservation:** `has_hole?(t) == false ⟹ has_hole?(erase(env, t)) ==
  false` — erasing a hole-free term never introduces a hole (erasure only removes
  and structurally recurses; it must not synthesise a `{:hole,_}`). Violation
  `{:hole_introduced, t}`.
- **Selective drop (differential vs `ctor_quantities`, the core soundness
  property):** for `{:ctor, c, args}` with quantity vector `qs`, `erase`'s kept
  arguments are **exactly** the `args` at `:present` positions of `qs` (each
  recursively erased). Dropping a `:present` position (runtime-data loss) or
  keeping an `:erased` position (zero-footprint violation) is
  `{:violation, {:wrong_positions_kept, c}}`. This is the direct differential
  against the locked `{0,ω}` decision.
- **Structural validity preservation:** `Cure.Core.Term.valid?(t) ⟹
  Term.valid?(erase(env, t))` — erasure yields a structurally well-formed Core
  term. (Full **kernel** acceptance-at-a-runtime-type is a non-goal — an erased
  term is a non-dependent runtime form that need not re-typecheck at the original
  dependent type; the umbrella's "where a runtime type applies" hedge. V4a asserts
  structural validity, the checkable invariant.) Violation `{:erase_ill_formed, t}`.

### V4b — `Relevance.check/4` (known-label differential; oracle = construction)

- **Relevant-use rejection (soundness):** a body that **by construction** uses an
  `:erased` binder at a relevant site must be **rejected** —
  `check(env, name, qs, body) == {:error, {:erased_used_relevantly, %{site: s}}}`
  for the intended site `s`. A `:ok` on such a body is
  `{:violation, {:relevance_unsound, site}}` — an erased binder leaking into
  runtime-relevant position, exactly the zero-footprint hole the check exists to
  prevent. One catalog entry per site (`:returned`, `:present_arg`, `:scrutinee`,
  `:applied`).
- **Clean acceptance (control):** a body that uses its erased binder only in
  erased positions (or not at all) must be accepted (`:ok`), so rejection is
  use-specific, not a blanket `:error`. A `{:error, …}` here is
  `{:violation, {:clean_body_rejected, name}}` (a construction-sanity assertion,
  per the V5 accept-control precedent).

## 4. Assay & injectable seam

New module `Antigen.Assays.Erasure` with `run/1` → `run/2` (op-map seam), mirroring
`Antigen.Assays.{Elab,Normalizer,Unifier,TotalityClosureAssay}`. Four assay ids:

| id | engine | property | oracle |
|---|---|---|---|
| `erasure/idempotent` | `Erase` | `erase∘erase == erase` + hole preservation | intrinsic |
| `erasure/selective` | `Erase` | keeps exactly `:present` ctor positions | `ctor_quantities` |
| `erasure/wellformed` | `Erase` | `valid?(t) ⟹ valid?(erase t)` | `Term.valid?` |
| `relevance/soundness` | `Relevance` | erased-used-relevantly ⟹ rejected | construction |

No `@assay_fuel`/`Conv` — `erase`/`has_hole?`/`check` are static structural walks
that terminate on their own; no term is evaluated.

**Op-map** (`@real`), injecting the **code-under-test** at the assay boundary:

```elixir
%{
  erase: &Cure.Elab.Erase.erase/2,
  has_hole?: &Cure.Elab.Erase.has_hole?/1,
  ctor_quantities: &Cure.Core.Inductive.ctor_quantities/2,
  valid?: &Cure.Core.Term.valid?/1,          # confirm exact name/arity in the plan
  relevance_check: &Cure.Elab.Relevance.check/4
}
```

Negative controls prove each assay load-bearing:
- `erasure/idempotent`: an `erase` stub wrapping its output in an extra ctor each
  call (never a fixpoint) → `{:erase_not_idempotent,…}`; and a stub returning a
  `{:hole,_}` on a hole-free input → `{:hole_introduced,…}`.
- `erasure/selective`: an `erase` stub that drops a `:present` position (or keeps
  an `:erased` one) → `{:wrong_positions_kept,…}`. (Injected via a `ctor_quantities`
  the assay compares against, kept real; the `erase` op is the weakened one.)
- `erasure/wellformed`: an `erase` stub returning a malformed term → `{:erase_ill_formed,…}`.
- `relevance/soundness`: a `relevance_check` stub returning `:ok` on a
  relevantly-using body → `{:relevance_unsound,…}`.

## 5. Generator

New module `Antigen.Generators.ErasureTerm` producing **fixed catalogs** (the
established fixed-catalog reconciliation — no Corpus/Coverage surgery; a lightweight
`:erasure_term` challenge kind, typespec-only, wired via `assay_module/1` + a
dedicated test):

- `erase_challenges/0` — Core terms + an env registering a ctor with a **mixed**
  quantity vector (`[:present, :erased]`) so `erase`'s selective drop is actually
  exercised (a ctor with an all-`:present` vector would make selective-drop
  vacuous). Covers idempotent / selective / wellformed ids. The env must register
  the ctor's quantities via the same path `Inductive.ctor_quantities` reads (open
  item #1 — likely `Inductive.declare/3`, the `Generators.SigMenu` template, since
  a bare-map ctor needs the right `quantities` field).
- `relevance_challenges/0` — Core bodies + `quantities` (with at least one
  `:erased` binder) for each of the four sites (`:returned`, `:present_arg`,
  `:scrutinee`, `:applied`), plus one clean-body control. Reuse
  `Antigen.Generators.ElabErasure`'s known relevant-use constructions where a
  Core-level body can be lifted from them (open item #2).

## 6. Invariants (what must never regress)

- No `Cure.Core.*`, `Cure.Elab.*` edits — reached read-only through the op-map. No
  `:meck`, no new dependency.
- `Antigen.Assays.Erasure` contains no literal `StreamData` token (the
  `architecture_test` grep — banked from V1's Stage-5 trip; comments too).
- Assay `run/1,2` returns only `:ok | {:violation, term()}` (matches the `@spec`
  and `Runner.replay_one/1`/`explore/1`'s no-catch-all dispatch). V4's
  incompleteness/reach directions are out of scope.
- The whole clean catalog re-checks `:ok` under the real ops (a real infection ⟹
  STOP and report; do not weaken a test). In particular, if the real `erase`
  keeps an `:erased` position or drops a `:present` one, that is a genuine V4a
  finding — report it.
- New generator atoms added to `Challenge.@known_atoms` (V5's §8-5 lesson).

## 7. Non-goals

- No fix to `Erase`/`Relevance` (V4 *finds*; a surfaced infection is reported, not
  patched, without separate authorization).
- No duplication of the existing surface-program `elab/erasure` assay (which tests
  the relevance rule end-to-end through elaboration) — V4b tests `Relevance.check/4`
  directly on Core bodies.
- **No** kernel-acceptance-at-runtime-type differential for `erase` (an erased term
  is a non-dependent runtime form that need not re-typecheck at the original
  dependent type; V4a asserts structural `Term.valid?` instead — §3).
- No auto-promotion or any change to the locked `{0,ω}` semantics — V4 tests the
  decision as locked, it does not revisit it.
- No random term fuzzer — a curated fixed catalog (elab pattern).
- No SMT (that is V6).

## 8. Open items (for the plan / review to pin)

1. **Ctor-quantity registration in the generator.** Pin the exact env construction
   that makes `Inductive.ctor_quantities(env, :MkPair)` return `[:present, :erased]`
   (or similar mixed vector) — trace `Inductive.declare/3` and the ctor record's
   `quantities` field (`ctors :: %{name => %{…, quantities}}`, verified in V5), and
   whether `Generators.SigMenu.env_of` or a direct `Inductive.declare` is the right
   template. The selective-drop differential is vacuous without a mixed vector.
2. **Core-body relevant-use construction for each site.** Pin the exact Core `body`
   term (with de Bruijn `{:var, k}` referencing an `:erased` binder) that triggers
   each `Relevance` site: `:returned` (erased binder is the body's result),
   `:present_arg` (passed in a `:present` position of a call/ctor), `:scrutinee`
   (matched in a `:case`), `:applied` (applied as a function head). Confirm against
   `Relevance`'s `walk/4` clauses which term shape hits each site, and confirm the
   `quantities` argument shape `check/4` expects (the binder-position → `:erased`
   mapping).
3. **`Term.valid?` exact name/arity** — confirm the structural-validity predicate
   in `lib/cure/core/term.ex` (name may be `valid?/1` or similar) for the
   `erasure/wellformed` op-map and the `valid?(t) ⟹ valid?(erase t)` guard (only
   assert on catalog terms that are themselves `valid?`).
4. **Challenge kind + atoms.** Add a `:erasure_term` kind (typespec-only) unless
   `:elab_program`'s payload can carry a Core term + env (it cannot — it carries
   surface source); add every generated ctor/def/binder name to `@known_atoms`.

## 9. Test catalog (for the plan — §5 of the plan will expand each)

1. V4a idempotent baseline: `erase(erase(t)) == erase(t)` on a mixed-quantity ctor term → `:ok`.
2. V4a hole-preservation baseline: hole-free term stays hole-free → `:ok`.
3. V4a idempotent negative control: wrapping `erase` stub → `{:erase_not_idempotent,…}`.
4. V4a hole negative control: hole-introducing `erase` stub → `{:hole_introduced,…}`.
5. V4a selective baseline: erase keeps exactly the `:present` ctor positions → `:ok`.
6. V4a selective negative control: `erase` stub dropping a `:present` position → `{:wrong_positions_kept,…}`.
7. V4a wellformed baseline: `valid?(erase t)` on a valid t → `:ok`.
8. V4a wellformed negative control: malformed-output `erase` stub → `{:erase_ill_formed,…}`.
9. V4b relevance baseline: one rejected body per site (`:returned/:present_arg/:scrutinee/:applied`) → `:ok`.
10. V4b clean-body control: erased binder used only in erased position → accepted → `:ok`.
11. V4b relevance negative control: `:ok`-returning `relevance_check` stub on a relevant body → `{:relevance_unsound,…}`.
12. Generator+wiring: each catalog non-empty & correctly tagged; `Runner.replay_one/1` dispatches all four ids and the whole clean catalog is `:ok`.

## 10. Next (umbrella roadmap)

After V4: **V6 SMT lint** (framed by the locked "Z3 out of the TCB" decision) is the
last umbrella vertical. **No auto-merge.**
