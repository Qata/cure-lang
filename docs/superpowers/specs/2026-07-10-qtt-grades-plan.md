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

- [ ] **2. Core binder reshape (TCB).**
      `Term` (`term?/1`, `shift/3`, `subst/3`, `has_free_var?/2`,
      `to_external/1`, `from_external/1`), `Value` (`{:vpi, g, dom, cl}`,
      `{:vlam, g, dom, cl}`), `Eval`, `Quote` (round-trip the grade), `Conv`
      (**compare by equality**), `Kernel` (`infer`/`check` on `:pi`/`:lam`/`:let`;
      checking a λ against a `vpi` must match grades), `Serialize`, `Normalise`,
      `MetaCheck`, `Certificate`, `Validator`, `Builtins`, `Inductive`.
      *Antibody:* `kernel/grade_conv` — a grade mismatch on otherwise-identical
      Π types must be REJECTED by conversion, and accepted when grades agree.
      Mutation-validate it: make `Conv` ignore the grade, prove the antibody
      fires, restore.
      *Done when:* full suite green, full Antigen campaign 0 infections,
      `Term.term?/1` rejects every 3-tuple binder.

- [ ] **3. Mechanical migration** of the 866 non-TCB sites (elab, antigen, test).
      Flip `validator.ex`'s already-reserved `grade_on_binders` rule from `:off`.
      *Done when:* no `{:pi, _, _}` / `{:lam, _, _}` / `{:let, _, _, _}` construction
      survives anywhere; the validator rule is on and green.

- [ ] **4. Usage check (E layer).** Generalise `relevance.ex` from `{0, ω}` to the
      full carrier: `Grade.admits?/2` for the used-vs-declared rule (Idris
      `LinearCheck.idr:274-276`, generalised — this is where affinity enters) and
      `Grade.mul/2` to scale a usage context on entering a subterm.
      *Red tests to write first:* using a `1` binder twice is rejected; using it
      zero times is rejected; using an `affine` binder zero times is ACCEPTED;
      using it twice is rejected; an `ω` binder is unconstrained; an erased binder
      in a relevant position is rejected (existing behaviour, must not regress).
      *Hazard:* a linear binder captured by a non-one-shot closure. `mul/2` is
      what makes that fall out — do not special-case it.

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

The remaining sibling defect is the **join-point residual**: `elaborate_match`
copies a continuation into every branch. It is a `match` problem, not a `let`
problem, and it wants the same treatment (share, don't copy). It does not block
slices 2–5, but a linear value used in a shared continuation would be
miscounted — so **slice 4 must either fix join points or reject linear values in
a duplicated continuation.**

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
