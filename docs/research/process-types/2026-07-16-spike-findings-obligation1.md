# Spike findings — obligation (1), first roadblocks

*2026-07-16. The §6 spike from `2026-07-16-otp-metatheory-in-cure-brief.md`, run
against the Cure elaborator. Records what typechecked, the two roadblocks the
spike hit, and what each cost. This is the input to the capability-expansion spec
(brief §6/§8). Branch: `otp-metatheory` (off `feature/idris-parity` HEAD).*

Repro modules live in `docs/research/process-types/spike/` (scratch, not preloaded).
Each was pushed at the elaborator with `Cure.Elab.Program.elaborate/1`.

## What was proved (all ACCEPT)

| Probe | File | Result | What it establishes |
|-------|------|--------|---------------------|
| (a) large elim `ReplyOf : Req -> Type` | `spike1`, `spike2` | ACCEPT | Type-valued match on a user ADT works, incl. a ctor with a field and stdlib Int/Atom/String replies. (Already regression-tested by `test/oracle/largeelim/le01`.) |
| (b) dependent return `handle(r) -> ReplyOf(r)` | `spike1`, `spike2`, `spike7_return_control` | ACCEPT | Each branch body is checked against `ReplyOf` reduced *after* the scrutinee refines. The **return/motive** refines per branch. |
| linear surface grade, consume-once | `spike3` | ACCEPT | `c :linear T` on a fn binder parses and accepts a once-consuming body. |
| linear neg-controls (drop / dup) | `spike3_neg_drop`, `spike3_neg_dup` | REJECT ✓ | `:usage_violation` — dropping (`used: :erased`) and duplicating (`used: :unrestricted`) a linear binder are both caught. |
| linear usage JOINED across branches | `spike4` | ACCEPT | A linear binder used once *per branch* of a match on another scrutinee = once total. QTT joins (max), does not sum. |
| linear one-branch-drops | `spike4_neg_branch_drop` | REJECT ✓ | A path that forgets to consume is ill-typed — exactly "consumed on every path". |

**Takeaway:** every *individual* ingredient of obligation (1) already works — large
elimination, dependent returns, and a sound linear discipline (enforced in
`lib/cure/elab/relevance.ex`, independent of the application path). The brief's
*predicted* first roadblock ("surface grades on binders are deferred") is **not**
a wall for a capability passed as a function parameter: the grade syntax exists and
is enforced.

## Roadblock #1 — FIXED (E-layer, non-TCB)

**Symptom:** the full obligation-(1) program (`spike5`) and even a bare
`{t:Type}` + `c :linear Box` callee (`spike6_call_linear_implicit`) *crashed* —
`FunctionClauseError` in `Cure.Elab.Elaborator.bidir_app_slot/5`.

**Diagnosis:** `bidir_app_slot/5` (the implicit-insertion application path, taken
whenever a callee has a leading implicit `{...}`) had clauses only for `:erased`
(insert a fresh meta) and `:unrestricted` (consume one supplied arg). A `:linear`
(or `:affine`) *explicit* param matched no clause and raised. Localized: the
plain-application path (`spike6_call_linear_plain`, no leading implicit) already
accepted a linear param — only the implicit-app iterator lacked the grade.

**Fix:** generalize the two `:unrestricted` clauses to
`when grade in [:unrestricted, :linear, :affine]`, mirroring the established idiom
in the constructor-argument twin `solve_arg/3` (`elaborator.ex:6669/6678`). At this
stage the grade governs later *usage counting* (`relevance.ex`), not slot
mechanics, so consuming the slot launders nothing — proved by the regression test
"linearity is STILL enforced through the implicit-app path (drop rejects)".

**Cost:** ~2 lines + guard, one file (`lib/cure/elab/elaborator.ex`). Not TCB (the
kernel re-checks the assembled signature). Red-green in
`test/cure/elab/pi_grade_source_test.exs`. Turned a crash into a real verdict —
which surfaced roadblock #2.

## Roadblock #2 — OPEN (the real blocker for obligation (1))

**Symptom:** with #1 fixed, `spike5` returns a clean
`{:error, {:index_mismatch, {:cannot_unify, ReplyOf(var 1), Reply0}}}`. Minimal
isolation `spike7_sibling_refine` returns `:branch_type`.

**Diagnosis:** Cure's dependent `match` refines the **return/motive** over the
scrutinee but **not the types of sibling context binders** that depend on it.
Matching `r : Req` against `GetCount()` reduces `ReplyOf(r)` in the *return*
position (control `spike7_return_control` ACCEPTs) but leaves a sibling binder
`w : ReplyOf(r)` — and, in `spike5`, `cap : ReplyCap(r)` and hence `reply`'s
inferred `{r}` — at the abstract `r`. So `v : ReplyOf(r)` never reduces to the
branch's concrete reply type.

This is exactly brief §8 roadblock #2 — dependent-match coverage / the "Lean-shape
matching" algorithm (`docs/superpowers/specs/2026-07-02-lean-shape-matching-design.md`,
`2026-07-02-dependent-match-surface-design.md`), whose incompleteness the brief
flagged as the most likely wall. It is a genuine E-layer capability gap
(context/telescope refinement on `match`, à la Idris/Agda generalizing the whole
dependent context over the scrutinee), not a grade or application-path issue.

**Reach-pin:** `test/cure/elab/pi_grade_source_test.exs` asserts the current
`{:error, {:index_mismatch, _}}` for `spike5`, to be flipped to `{:ok, _}` when
context-refinement-on-match lands.

## Next step

Obligation (1) is blocked solely on roadblock #2. Per brief §8, this warrants a
focused capability-expansion spec: **refine the types of scrutinee-dependent
sibling binders during dependent `match`** (motive generalization over the
dependent context, not just the return). Verify Idris/Agda alignment; the machinery
overlaps `abstract_term` / `build_motive` (the same used by `rewrite` and
`with`-abstraction). Obligation (2) (F-1 send-safety) is untouched and independent.
