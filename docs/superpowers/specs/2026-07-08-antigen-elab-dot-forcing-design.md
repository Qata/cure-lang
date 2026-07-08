# Antigen elab-tier dot-forcing vertical — design

**Date:** 2026-07-08
**Initiative:** F (task #16), queued behind #12 (dot-syntax tail) for execution.
**Layer:** A (Antigen) only — no elaborator, kernel, or parser changes. Pure test-side addition.

## 0. Why: the oracle-boundary blind spot

The existing `forcing/dot` vertical (`Antigen.Assays.DotForcing`, ledger row #24) is a
**value-level known-label oracle**: it builds a kernel context from the v1 sig menu,
computes the branch-unify substitution, and calls the named-implicit check directly
through the `Cure.Elab.Elaborator.forced_check_probe/7` shim. Its entry point is *below*
the check's call sites.

The C-a defect (ledger row #5 tail, fixed by #12's Task 2) was a **call-site omission
one level up**: `elaborate_matched_branch` routed carried-eq branches to
`elaborate_carried_eq_branch`, which never invoked `check_named_implicits` at all. The
value oracle is structurally blind to this class:

1. Every challenge it generates calls the check *by construction* — it can never
   observe a caller that forgets to.
2. The condition selecting the carried path (a sibling whose type mentions the
   scrutinee's stuck index, detected by `detect_carried_index`) is not representable
   in its payload space (family, ctor, indices, name, written term). No payload makes
   the shim take or skip a dispatch path the shim does not have.

The fix is not to bend that assay but to add challenges **one tier up**, entering at
`Cure.Elab.Program.elaborate/1` — and that tier already exists: `Antigen.Assays.Elab`
consumes `:elab_program` challenges carrying raw surface source (`elab/completeness`,
`elab/metamorphic`, `elab/erasure`, `elab/soundness`). This design adds a dot-forcing
generator family to it. The `elab/erasure` family is the direct precedent: a two-sided
`expect:` catalog plus a metamorphic `:same`/`:flip` relation form.

**Rejected alternative** (recorded for the endgame): raising `forced_check_probe`'s
entry point to `elaborate_matched_branch`. That function carries ~12 arguments of
elaborator-internal state; a shim reconstructing that state drifts from the real caller
— exactly the failure mode the #12 plan review caught (the plan wrongly assumed the
probe called `check_named_implicits`; it reimplements it inline and had already
diverged once). The value oracle stays as the unit tier for the check function itself;
this vertical is the integration tier for its call-site wiring.

## 1. Design overview

Two small additions, mirroring the `ElabErasure` shape verbatim:

- **`lib/antigen/generators/elab_dot_forcing.ex`** (`Antigen.Generators.ElabDotForcing`)
  — a deterministic fixed catalog (no corpus banking, like `ElabComplete`/`ElabErasure`)
  of self-contained surface modules with two-sided expected verdicts, plus metamorphic
  `:same`/`:flip` variants.
- **Two new `run/1` clauses in `lib/antigen/assays/elab.ex`** for assay
  `"elab/dot_forcing"` — a catalog clause (verdict must equal `expect`) and a relation
  clause (`:same` / `:flip`), mirroring the two `elab/erasure` clauses, with distinct
  violation tags.

The known-label discipline survives the move up the stack because the **generator
writes both the forced solution and the written dot value itself**: matching `hmk`
against `H(S(j), …)` pins `m := j`, so a catalog entry that writes `{m = .j}` is
accept-by-construction and one that writes `{m = .(S(j))}` is reject-by-construction.
No reference oracle (Idris) is consulted at assay time.

## 2. The catalog

### 2.1 Axes

The catalog is the product of the two axes the C-a class demands, plus the C-c
quantity axis:

- **Dispatch path**: `plain` (ordinary solved-verdict branch) × `carried` (a sibling
  `w : G(app(p, q))` forces `detect_carried_index` to fire — the mixed forced+carried
  `H`/`app`/`G` shape from #12's Task 2).
- **Dot outcome**: `right` (written value = forced solution → accept) × `wrong`
  (written value ≠ forced solution → reject, error head `:forced_pattern_mismatch`).
- **Unforced quantity (C-c)**: `bind_erased` (unforced named implicit bound and used
  only erasedly → accept) × `bind_relevant` (bound and used in a computationally
  relevant position → reject, error head from the Relevance check).

Eight cells total: {plain, carried} × {right, wrong} for the forced axis, and
{plain, carried} × {bind_erased, bind_relevant} for the unforced axis. Every cell's
label is correct-by-construction; the carried column is precisely what no existing
Antigen challenge could reach.

### 2.2 Sources

Catalog surface programs **reuse the shapes landed by #12** — the unit-test fixtures
of #12 Tasks 2/4 and the oracle fixtures ni03/ni05/ni06/ni07 — rather than inventing
new ones. This keeps the randomized tier and the deterministic oracle tier pinned to
the same programs (a divergence between them would itself be diagnostic). The carried
preamble is the `H`/`app`/`G` menu:

```
type SList = SNil | SCons(Nat, SList)
fn app(xs: SList, ys: SList) -> SList = match xs
  SNil() -> ys
  SCons(h, t) -> SCons(h, app(t, ys))
type H indices (n: Nat, xs: SList)
  hmk : H(S(m), app(as, bs))
type G indices (xs: SList)
  gwrap : G(cs)
```

with probe fns of the #12 Task-2 shape (`v: H(S(j), app(p, q))` scrutinee; the
carried variant adds the sibling `w: G(app(p, q))`, the plain variant omits it). The
unforced cells reuse the ni05/ni06 `Vec`/`P`-style shape. The plan copies the exact
landed fixture text at implementation time; if a landed fixture differs from this
spec's sketch, **the landed fixture wins**.

### 2.3 Payload and expected-error hardening

Catalog challenge payload: `%{id, src, expect}` with `label: expect`
(`:accept | :reject`), matching `ElabErasure`. Reject cells additionally carry
`expect_error:` — the expected error head atom (e.g. `:forced_pattern_mismatch`,
`:named_implicit_unforced`). The assay checks the head when present, so a fixture that
rots into rejecting for an unrelated reason (parse error, arity error) is a violation
(`{:dot_forcing_wrong_reject_reason, id, got}`), not a silent pass. The pinned error
shape `{:named_implicit_unforced, name}` (2-tuple) is matched, never changed.

### 2.4 Metamorphic forms

- **`:flip` — the C-a detector.** Each accepting base is paired with a
  verdict-flipping mutation that must turn accept into reject:
  - `corrupt_dot`: rewrite the written dot value (`{m = .j}` → `{m = .(S(j))}`) on
    both the plain and the carried base. On pre-#12 code the carried instance of this
    relation FAILS (the variant still accepts because the carried path skipped the
    check) — this single challenge is the one that would have caught C-a.
  - `promote_use`: on a `bind_erased` base, rewrite the body to use the bound name in
    a relevant position — proves the C-c quantity gate is load-bearing on each path.
- **`:same`.** Typing-preserving perturbations must not change the verdict:
  α-rename and prepend-unused-implicit-param, following `ElabComplete.variants/1`
  (arm reorder is inapplicable — the menu families are single-constructor). Applied
  to each catalog base.

Relation payload: `%{id, transform, relation, base_src, variant_src}` — same shape as
`elab/erasure`'s relation form.

## 3. Assay clauses

Added to `Antigen.Assays.Elab` (they mirror the `elab/erasure` clauses; the
duplication is deliberate — one clause per assay family with distinct violation tags
is the file's existing style):

- Catalog: elaborate `p.src`, collapse to the accept/reject bit; violation
  `{:dot_forcing_verdict_wrong, id, %{expected, actual}}` on mismatch. When
  `expect_error` is present and the verdict is a reject, the error head must match
  (see §2.3).
- Relation: elaborate base and variant; `:same` requires equal bits, `:flip` requires
  `base == :accept and variant == :reject`; violation
  `{:dot_forcing_relation_wrong, id, transform, %{relation, base, variant}}`.

A raised exception inside `elaborate/1` is already normalized by the existing
`elaborate/1` helper in the assay module and counts as reject for the bit — consistent
with `elab/erasure`.

## 4. What does not change

- `lib/antigen/assays/dot_forcing.ex` + `lib/antigen/generators/dot_forcing.ex` (the
  value-level unit tier) — untouched by this work. Its moduledoc's "does NOT cover the
  carried-eq motive branch" honesty note gets a one-line pointer to this vertical
  **only if** #12's Task 6 has not already rewritten that moduledoc; never edit it
  concurrently with #12.
- No changes under `lib/cure/` at all. If implementation discovers an elaborator
  behavior contradicting a catalog label, that is a STOP-and-report (it means either
  #12 landed differently than planned or a genuine infection) — not a license to
  patch the elaborator in this chain.
- The existing `elab/*` families, their generators, and their tests.

## 5. Wiring and execution points

Challenges execute wherever `ElabErasure`'s do: a dedicated deterministic test file
(`test/antigen/generators/elab_dot_forcing_test.exs`, mirroring
`test/antigen/elab_erasure_test.exs`'s structure) that runs every catalog and relation
challenge through `Antigen.Assays.Elab.run/1` and asserts `:ok`, plus
assay-discrimination tests (see §6). At plan time, grep for every execution/registration
point that references `ElabErasure` (runner, e2e, corpus, health gates) and mirror each
one; the spec requirement is **parity of wiring with `elab/erasure`**, whatever that
set turns out to be.

## 6. Testing the vertical itself (red-green discipline)

The deliverable is test infrastructure, so the red-green cycle targets the vertical's
own discrimination (mirroring `elab_completeness_test.exs`):

1. **Generator unit tests** (red first: module absent): catalog size and cell coverage
   (all eight cells present, each axis value represented), every `src` elaborates to
   its `expect` bit — this is also the end-to-end proof the fixtures are live post-#12.
2. **Assay discrimination**: a hand-built challenge with a deliberately wrong `expect`
   must yield the catalog violation; a relation challenge with `variant_src ==
   base_src` under `:flip` must yield the relation violation; a reject-for-the-wrong-
   reason source (e.g. a syntax error) with `expect_error` set must yield
   `{:dot_forcing_wrong_reject_reason, …}`.
3. **No new full-suite gate semantics**: the new test file joins the ordinary
   `mix test` set; the Antigen campaign gate covers it via the wiring-parity of §5.

Tests are behavioral and immutable once green.

## 7. Sequencing and constraints

- **Execution is gated on #12 completing** (its executor owns the one-build slot and
  the catalog labels assume post-C behavior: pre-Task-2 code makes the carried cells'
  labels wrong by design). Spec/plan/review stages may proceed concurrently — they are
  doc-only.
- File-collision audit vs #12: this work creates `elab_dot_forcing.ex` (new),
  `elab_dot_forcing_test.exs` (new) and appends clauses to `assays/elab.ex` — none of
  which #12 touches. The §4 moduledoc pointer is the only potential overlap and is
  explicitly deferred until after #12 lands.
- Standard batch constraints apply: ghost commits, explicit-pathspec staging, one
  `mix` invocation at a time, two-pipeline steer in any subagent brief (the dependent
  machinery is `lib/cure/elab/*` + `lib/cure/core/*`; `lib/cure/compiler/*` and
  `lib/cure/types/*` are decoys).

## 8. Generality

This establishes the reusable pattern for **call-site-wiring properties** that value
shims structurally cannot probe: enter at `Program.elaborate/1` with
correct-by-construction labels, and encode "the check is actually invoked on path P"
as a `:flip` relation whose mutation targets exactly the checked property. Future
candidates (not in scope): splice-site reconstruction (C-b class), dispatch
inheritance for future branch kinds, guard-check wiring once match-embedded guards
land.
