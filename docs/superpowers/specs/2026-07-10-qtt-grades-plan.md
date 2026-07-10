# QTT Graded Binders — Implementation Plan

**Branch:** `core-let-binder`
**Goal:** full Quantitative Type Theory (Atkey) with `{0, 1, affine, ω}` grades on
Core binders, so linear *and* affine types land on one mechanism.
**Authority:** Idris (`~/Develop/Idris2`), which abstracts its quantity behind
`Algebra.Semiring` + `Algebra.Preorder` and instantiates `ZeroOneOmega`. Cure
instantiates a four-element carrier. Pre-approved under the standing
TCB-alignment directive (`tcb-change-blanket-approval`).

---

## Settled decisions — do not relitigate

1. **Grade is the FIRST field.** `{:pi, g, dom, cod}`, `{:lam, g, dom, body}`,
   `{:let, g, ty, val, body}`. This is not a fresh choice: `validator.ex:125,128`
   already reserves exactly these shapes ("the future graded 4-tuple forms are
   matched so the walker survives the later grade reshape").

2. **ONE canonical spelling.** Never leave a 3-tuple and a 4-tuple form of the
   same binder coexisting. Two spellings of one binder diverge *below* the typing
   judgement — the recorded `ctor-spelling value dichotomy` bug class.

3. **Grades are opaque.** Nothing outside `Cure.Core.Grade` pattern-matches a
   grade. Go through `add/2`, `mul/2`, `admits?/2`, `leq/2`, `erased?/1`,
   `present?/1`, `restricted?/1`. This is what keeps the carrier extensible.

4. **`Conv` MUST compare grades.** Idris `Core/Normalise/Convert.idr:328`:
   `if sameBinders bx by && multiplicity bx == multiplicity by`. So
   `(1 x : A) -> B` is a *different type* from `(x : A) -> B`. Comparison is by
   **equality**, never by the preorder — `leq/2` belongs to the usage check, not
   to conversion.

5. **The usage check stays OUT of the kernel.** Idris keeps `LinearCheck.idr`
   outside `Core.Normalise`. Cure keeps it in the E layer (`relevance.ex`
   generalised). The kernel *carries and compares* grades; it does not *count*
   uses.

6. **`:let` gets a grade too**, uniformly with `:pi`/`:lam` (Idris `Binder.idr`
   grades `Lam`, `Pi`, `Let`, `PVar`, `PLet`). This retires the deliberate
   omission made when `:let` landed (`a84c454`).

7. **Default grade is `:unrestricted`.** Every existing 3-tuple site migrates to
   `:unrestricted`, which is behaviour-preserving.

8. **`:lam` IS graded, even though it doubles the migration.** Considered and
   REJECTED: grading only the types (`:pi`, `:vpi`, `:let`) and leaving `:lam` a
   3-tuple. That is 380 sites instead of 1029, and it looks sound at slice 2 —
   `Conv` only ever compares *types*, a λ's grade is redundant with its Π's, and
   `Kernel.infer` on a λ could default to `ω` (the elaborator can never infer a
   bare lambda anyway, so λs always arrive in checking mode).

   It breaks at **slice 4**, which is how a soundness hole ships. `relevance.ex`
   learns a binder's quantity from the **def's parameter vector**, so it only
   knows *top-level* params. An **inner** λ binding a linear variable —
   `fn(1 c: Chan) -> Effect(Unit)`, exactly a `spawn` body — would be invisible to
   the usage check, and its linear binder silently unchecked. Idris stores the
   multiplicity on `Lam` for precisely this: `LinearCheck.lcheck` reads
   `multiplicity b` off the binder (`Core/LinearCheck.idr`, `lcheckBinder`).

   Site split, measured post-merge: `:pi` 315, `:vpi` 18, `:let` 47 (= 380);
   `:lam` 634, `:vlam` 15 (= 649). Total 1029.

---

## Blast radius (measured 2026-07-10)

Re-measured after merging `feature/idris-parity` (2026-07-10, tree at 3795 tests
green):

| area | binder sites | nature |
|---|---|---|
| `lib/cure/core/` | 76 | **TCB. Reviewed diff.** |
| `lib/cure/elab/` | 92 | mechanical |
| `lib/antigen/` | 339 | mechanical (generators construct binder literals) |
| `test/` | 435 | mechanical |
| `types/`, `compiler/`, `mix/` | 13 | classic pathway; check whether it even sees Core binders |

**Hazard:** Elixir will not error on a stale 3-tuple `{:pi, a, b}` — it falls
through to a catch-all and behaves silently wrong. The nets are `Term.term?/1`
(reject 3-tuples once migrated), the `Validator`, and the 3694-test suite. Do not
rely on the compiler.

---

## Slices

Each slice is independently gated and independently committable. Never commit a
half-migrated tree.

- [x] **1. `Cure.Core.Grade`** — the semiring. `4050c81`.
      Laws checked exhaustively over the finite carrier (all 64 triples):
      additive commutative monoid, multiplicative monoid, `0` annihilates, both
      distributive laws, preorder reflexive/transitive with `ω` as top.
      Pinned asymmetries: `erased ⊀ linear` (a linear value must be used);
      `affine ⊀ linear` (an affine value may be dropped).

- [x] **2 + 3. Binder reshape + full migration (TCB).** LANDED.
      All Core binders are graded 4-/5-tuples; `Conv` compares grades by
      **equality**; `Kernel.check` rejects a λ whose grade differs from its Π's;
      `validator.ex`'s `grade_on_binders` rule flipped `:off` → `:reject`.
      1195 grades inserted across 150 files; 125 match sites converted.
      Antibody `kernel/grade_conv` (7 cells), mutation-validated both ways.

      **What the mechanical pass could NOT see, and what caught it:**
      * `wrap_binders(:pi, …)` / `wrap(:pi, …)` (elab) and
        `Generators.Serialization.binary(tag, …)` build the binder tuple from a
        **tag**. No textual pass sees those. `Term.term?/1` rejecting 3-tuples
        caught the first two at runtime; a generator round-trip test the third.
      * **`normalise.ex` was missed entirely.** `nf_struct({:vpi, dom, cl})` kept
        matching the ungraded shape, fell through a catch-all, and δ-normalisation
        silently stopped happening under a binder. Exactly one test caught it
        (`NfStuckCaseDeltaTest`). This is the fallthrough hazard, in the TCB.
        **Sweep every file in `lib/cure/core/` after any taxonomy change; do not
        trust a list of files you believe you edited.**
      * The blanket pass **corrupted tests that deliberately construct stale
        shapes** (`validator_test`, `grade_binder_test`). Those now build them with
        `:erlang.list_to_tuple/1` so no mechanical pass can "fix" them.

      **`lib/cure/types/` IS OFF-LIMITS.** It has its OWN, unrelated
      `{:pi, [{name, type, mode}], ret_ast}` — the *classic* pipeline's Pi, with
      `mode :: :explicit | :implicit | :erased`. The mechanical pass injected a
      Core grade into it, including into an `@type` spec. It compiled. Reverted.
      Two different `:pi` namespaces exist; only Core's is graded.

      **Metastatic is not a constraint.** Its MetaAST is `{type, keyword_meta,
      children}` and governs the *surface* AST (`Cure.Compiler.Parser`). Cure never
      calls Metastatic (`grep -rn "Metastatic\." lib/` → nothing). Core was never
      3-arity-uniform anyway: `{:var, k}` is 2-arity, `{:data, …}` and `{:case, …}`
      are 4-arity, `{:absurd}` is 1-arity.

      **Corpora needed migrating, idempotently.** `key=` (base64 s-expr) and
      `pieces=` (plaintext) in `corpus.sexp`/`seeds.sexp`/`coverage.sexp` plus
      `test/fixtures/core_conformance.txt` hold serialized binders. Scaffolds hold
      none (verified). `mix test` **banks seeds into the committed corpora**, so a
      run under the graded kernel leaves already-graded records behind and a blind
      regex double-inserts. The migration checks for an existing grade first, and
      asserts idempotence on re-application.

      *Gate:* 3813 passed / 0 failed. Antigen 314/314 cells, 400-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes.

- [x] **4a. Quantities are grades.** LANDED. Def/ctor `quantities` were the ad-hoc
      `:erased | :present` pair; `:present` (the ω one) is now `:unrestricted`, and
      `Inductive.quantity/0` IS `Grade.t/0`. 123 atoms renamed across 29 files.

      **The dangerous half was `Erase`.** It keeps an argument iff a runtime value
      exists for it, and asked `q == :present`. A blind rename turns that into
      `q == :unrestricted`, which **silently drops every `:linear` and `:affine`
      argument** from the emitted term. The predicate is `Grade.present?/1`
      (anything but `0`). Same trap in `Emit` (which params get real BEAM variable
      names vs `_e` placeholders) and three `Enum.count(.., & &1 == :present)`
      sites in the elaborator. Guarded by `test/cure/elab/quantity_grade_test.exs`,
      mutation-validated: the equality predicate fails 3 of 7.

      **Corpora again.** `:present` lives in `scaffold=` as a **binary string**
      leaf (35 records) and in `key=` as base64 text (369 records) — never in
      `pieces=`. The key rewrite MUST use a strict boundary regex: flags named
      `case_present` / `app_present` exist and a naive word swap corrupts them
      (271 preserved in `seeds.sexp`).

      *Gate:* 3820 passed / 0 failed. Antigen 314/314 cells, 300-run campaign → 0
      infections. Oracle replay 65/65. `mix dialyzer` passes.

- [ ] **4b. Usage check (E layer).** Generalise `relevance.ex` from `{0, ω}` to the
      full carrier: `Grade.admits?/2` for the used-vs-declared rule (Idris
      `LinearCheck.idr:274-276`, generalised — this is where affinity enters) and
      `Grade.mul/2` to scale a usage context on entering a subterm.
      *Red tests to write first:* using a `1` binder twice is rejected; using it
      zero times is rejected; using an `affine` binder zero times is ACCEPTED;
      using it twice is rejected; an `ω` binder is unconstrained; an erased binder
      in a relevant position is rejected (existing behaviour, must not regress).
      *Hazard:* a linear binder captured by a non-one-shot closure. `mul/2` is
      what makes that fall out — do not special-case it.

- [ ] **4c. Join points (E layer).** Bind a catch-all body **once** instead of
      re-elaborating it per uncovered constructor. Encoding uses only existing
      Core formers: wrap the `:case` in the `:let` binder slice 1 added, binding
      `j = {:lam, ω, S, e}` at type `{:pi, ω, S, R}` — literally the motive λ with
      `:lam` rewritten to `:pi` — and emit `{:app, j, scrut}` in each defaulted
      branch. The λ supplies the laziness a bare `:let` would destroy: the
      catch-all must not run when a real arm matches.
      *Scope:* only when the motive is **non-dependent** (its body has no free
      `{:var, 0}`) and **≥2** constructors are uncovered. A dependent motive would
      need the branch's reconstructed `C(args…)` — including its erased telescope
      args — rather than `scrut`, so it keeps today's expansion; one uncovered
      constructor makes a closure a pessimization.
      *Red tests to write first:* a 6-constructor type with one arm covered
      elaborates the catch-all body **once**, not 5×; two nested catch-alls give
      2 copies, not 25; a named catch-all `x -> g(x)` still sees the scrutinee's
      value; each constructor still normalizes to the same result it does today
      (semantics preserved); one uncovered constructor emits **no** join point; a
      dependent-motive match is unchanged and still typechecks.
      *Not a blocker for 4b* — see "Known prerequisite" above.

- [ ] **5. Surface syntax.** `fn f(1 x: T)`, `fn f(0 {n: Nat})`, an affine marker,
      and `let 1 c = spawn …`. Parser + elaborator. Default remains `ω`, so no
      existing source changes.

---

## Known prerequisite, already met

`let` no longer duplicates or discards its rhs (`9e7eeb2`): surface substitution
runs only at exactly one use, and `let x : T = e` binds a check-only rhs once.
Without that, a linear handle could be cloned *below* the usage check — the
elaborator would manufacture the aliasing the type system forbids. Slice 4 may
therefore proceed with no substitution-path escape clause.

The remaining sibling defect is the **join-point residual**. An earlier draft of
this plan described it as "`elaborate_match` copies a continuation into every
branch" and concluded that **slice 4 must either fix join points or reject linear
values in a duplicated continuation**. Both halves of that sentence were wrong.
The corrected, measured account:

**Where the duplication actually is.** Core `:case` has no default branch, so a
surface catch-all (`_ -> e` / `x -> e`) is expanded into one Core branch per
*uncovered constructor*, and `elaborate_default_branch/10` surface-substitutes
the catch-all's variable and **re-elaborates `e` from scratch each time**. Guards
are not the cause: `guard_chain/7` is already linear (its fall-through `ff` is
elaborated once), and `split_first_tuple_column/2` refuses to duplicate a row
(it bails to `:not_applicable` unless the first-column heads are distinct).
`fold_ctor_guard_groups/2` splices the closer per guarded group, but that is
subsumed by the catch-all expansion.

Measured on `elaborate/1`, counting occurrences of the catch-all body's callee in
the elaborated Core:

| shape | copies |
|---|---|
| 3-constructor type, 1 arm covered | 2 |
| 6-constructor type, 1 arm covered | 5 |
| two *nested* catch-alls, 6-constructor type | **25** |

So *k* nested catch-alls over an *n*-constructor type yield **(n−1)^k** copies —
exponential term growth, paid in flash on an ESP32.

**It is not a soundness problem.** Idris combines branch usages by *agreement*,
not summation (`LinearCheck.idr:528-540`, `combineUsage`): a `Use0`/`Use1`
mismatch across branches is an error, and `UseAny` wins over anything. Every copy
the expansion makes lands in a **disjoint constructor branch**, never
sequentially within one branch, so a linear variable in the copied body is still
counted **once**. Duplication cannot inflate `1` to `ω`. Slice 4b is therefore
safe with or without join points, and needs no escape clause.

Cure's `combine` must nevertheless be **grade-aware**, where Idris's is not.
Idris throws on a `Use0`/`Use1` mismatch regardless of the binder's grade because
Idris has no affine quantity. For Cure, a `:affine` binder used in one branch and
dropped in another is **legal** — affine may be dropped. The rule is
`Grade.admits?(declared, uses_in_branch)` checked **per branch**, not on a summed
count.

Join points are therefore a **term-size fix, not a soundness fix** — tracked
below as slice 4c on the operator's direction.

---

## Discipline (from `cure-porting`)

- Red-green: a named failing test before every fix. **A test that passes with and
  without the change is vacuous** — delete it and drop the claim. (This already
  bit us once: the `Certificate` "blind spot" tests were vacuous and the claimed
  soundness hole did not exist.)
- TCB changes: red→green, new Antigen antibody **mutation-validated** (break it,
  prove it fires, restore), full Antigen campaign, full `mix test`.
- Ghost commits, explicit pathspec staging. Revert `test/antigen/seeds.sexp`
  noise before committing — `mix antigen` banks seeds into a committed corpus,
  including from runs where the kernel was deliberately broken.
- One `mix` at a time.
- `Antigen.Runner.@group_table` is indexed by generator POSITION. **Append** new
  generators; a mid-list insert silently renumbers the rest and adaptive
  reweighting bumps the wrong ones.
