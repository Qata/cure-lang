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

## Roadblock #2 refined — the `with` construct already refines siblings

Cure has an EXISTING construct that does sibling refinement: `with <scrut> [proof
<name>] | C(pat) -> body` (`elaborate_with_value`, elaborator.ex:2629). For a
**non-indexed scrutinee family** it refines every in-scope sibling whose type
mentions the scrutinee, by Eq-arrow transport in the branch body. `Req` is
non-indexed, so:

- `spike8_sibling_with` (sibling `w : ReplyOf(r)` via `with r`): **ACCEPT**. The
  dependent typing that plain `match` lacked is fully available through `with`.
- `spike9_obligation1_with` (obligation (1) via `with r`): the `:index_mismatch`
  is GONE — the dependent typing now works. It fails only on
  `{:usage_violation, used: :unrestricted, declared: :linear}` for `cap`.

## Roadblock #2b — the real remaining wall: linearity through sibling transport

**Diagnosis (root cause found).** `with`'s sibling transport
(`elaborate_with_eq_branch`, elaborator.ex:3011) encodes each branch as an
immediately-applied nest of **ω-graded** lambdas —
`(case r of {c, ar, λprf. (λh'. body) transport}…) (refl r)` — where
`transport = transport_case(prf,…) cap`. The erasure-soundness checker
`lib/cure/elab/relevance.ex` then over-counts `cap`:

- a `:lam` body's use of an outer binder is scaled by ω (relevance.ex:239 — "a λ may
  be entered any number of times"), so the `λprf` wrapper ω-scales `cap`;
- an argument to a bare λ / a `:case`-headed application is scaled by the callee's
  grade, which defaults to ω for a `:case` head (`callee_quantities`, relevance.ex:624)
  and for the `λh'` rebind — so `cap` is ω-scaled again.

At RUNTIME the proof and transport erase away (`Equivalent` is collapsible; the
transport is J/subst on `refl`), leaving `case r of … cap …` with `cap` used once
per path. So this is a **precision gap in relevance** (it rejects a term that
`Erase` makes linear-safe), NOT a real linearity violation. relevance.ex is E-layer
(explicitly "NOT the kernel") but soundness-critical (it makes erasure sound), with a
documented red-team history — so the fix must be provably sound, not a hack.

**Design options** (both need relevance to stop ω-scaling the one-shot convoy):
1. *Convoy precision in relevance.* Recognize the McBride convoy
   `{:app, {:case,…branches…}, arg}` (a case returning a function, immediately
   applied) as one-shot, and scale the arg by the branch-lambda **parameter grade**
   rather than ω (`callee_quantities` of a `:case` head = the uniform branch-λ
   grade). Encoding-agnostic; mirrors `Erase`. Must stay sound for an adversarial
   convoy (`(case s of λx:ω. dup(x,x)) lin` must still REJECT — scaling by the ω
   branch grade does reject it).
2. *Motive-generalize the sibling instead of transporting it.* Abstract the linear
   sibling into the case motive (`motive = λw. Π(cap : ReplyCap(w)). G`, applied to
   `cap`), giving `(case r of λcap':linear. body) cap` with NO `λprf`/transport.
   Cleaner for linearity, but the doc (elaborator.ex:2593-2596) notes motive-domain
   generalization tripped `Quote.reify`'s `{:vdata}` param/index collapse for an
   INDEXED family (`SNat(w)`); must verify a PARAM family (`ReplyCap(w)`) reifies.

Both converge on the same relevance fix (convoy arg scaled by the branch grade, not
ω) + making the sibling-binding λ carry the sibling's real grade. Option 2 also
removes the `λprf` ω-scale entirely, so it is the likely target.

## RESOLUTION — obligation (1) DISCHARGED (roadblock #2b sidestepped, not needed)

Roadblock #2b is real but it is NOT on the critical path. Obligation (1) is
expressible today by **splitting the two concerns** so no linear sibling is ever in
scope during a `match` (no convoy):

- `handle(r) -> ReplyOf(r)` — the per-constructor dependent reply VALUE (the spike1
  shape; the `match` lives here, with no capability in scope).
- `reply({r}, cap :linear ReplyCap(r), v: ReplyOf(r))` — the linear reply rule.
- `serve(r, cap) = reply(cap, handle(r))` — compose with `r` ABSTRACT, so
  `ReplyOf(r)` is definitionally itself and unifies with `handle(r)`'s type; the
  capability is used exactly once.

`spike10_split.cure` ACCEPTS. The three negative controls all REJECT:
`neg1_wrong_reply` (`:index_mismatch` — value not `ReplyOf(r)`), `neg2_drop_cap`
(`used :erased`), `neg3_dup_cap` (`used :unrestricted`). So the type rule genuinely
CONSTRAINS: a well-typed reply preserves the request's reply type and consumes the
capability exactly once.

**Trust anchor.** The `test/oracle/otp/` cluster mirrors the positive + three
negatives in Cure and Idris 2; `mix cure.oracle otp` reports `rel=same` on all four
(accept/accept, reject/reject ×3). Idris 2 has the same `1 x : T` multiplicity and
large elimination, so agreement localizes trust.

**Deliverable.** `lib/std/otp_proof.cure` (`Std.Otp.Proof`) — kernel-checked,
totality-certified, compiled into the stdlib every build. `raw_call`'s docstring in
`lib/std/otp_raw.cure` now points at it.

Roadblock #2b (linearity-preserving sibling refinement so the ERGONOMIC branching
handler `with r … reply(cap, …) per branch` type-checks) remains reach-pinned for a
future slice — it improves authoring nicety, not expressiveness. Root cause + two
sound design options are recorded above.

## Obligation (2) — DISCHARGED (strong operational form)

Send-safety for a clause-DERIVED pid message index (F-1), in `Std.Otp.Proof`:

- `type Pid(m: Type)` with `MkPid : ((m) -> Response) -> Pid(m)` — the pid CARRIES
  its handler, so its message index `m` is exactly the stored handler's DOMAIN.
- `spawn_actor({m}, handler: (m) -> Response) -> Pid(m)` — the index is DERIVED
  (the implicit `m` inferred from the handler), not annotated (NVLang's T-Spawn
  reads it off a receive annotation; this is the open half).
- `post({m}, p: Pid(m), msg: m) -> Response = match p | MkPid(h) -> h(msg)` — `post`
  requires `msg` at the derived type AND DISPATCHES it through the stored handler.

Operational send-safety: a well-typed `post` delivers to the handler the pid
carries, which must be TOTAL (kernel-certified exhaustive) to exist, so every
message of the derived type is handled. Negatives reject: `ob2_neg_wrong_msg`
(`:index_mismatch` — a message not of the actor's type), `ob2_neg_nontotal`
(`:missing_branch` — a non-exhaustive handler cannot form). `test/oracle/otp/`
mirrors all three in Idris, `rel=same`.

This needed one gap fix — **higher-order constructor fields**. A parenthesised
function-typed ctor field (`MkPid : ((m) -> Response) -> Pid(m)`) did not parse:
the GADT ctor grammar (`parse_type_atom`) is arrow-free so the ctor's own arrow
chain separates fields, but a `(...)`-grouped function type is unambiguous and is
now absorbed (`parse_paren_arrow_tail`, parser.ex). The elaborator already handled
such fields; the gap was purely the parser.

## Roadblock #2b — RESOLVED (ergonomic branching handler)

The branching handler `with r … reply(cap, …) per branch` now type-checks, with
linearity enforced (drop / dup in a branch reject). Two changes:

1. **Elaborator — motive-generalization** (`elaborate_with_motivegen_branch`,
   single sibling, no user proof): the sibling refinement no longer uses
   Eq-transport (`transport_case(prf) cap`, a collapsible case that erases to
   identity but which relevance ω-scaled pre-erasure — hostile to linear accounting
   in BOTH directions). Instead the sibling becomes a Π domain in the motive
   `λw. Π(h': H[e↦w]). G[e↦w]` and a real λ binder per branch, and the case is
   applied to the original sibling: `(case r of λcap'. body) cap`. The `Π(ReplyCap(w))`
   domain reifies cleanly — `ReplyCap` is a PARAM-only family, so the doc's warned
   param/index collapse (for index-bearing `SNat(w)`) does not apply.
2. **Relevance — the McBride convoy rule** (`walk_convoy`): `(case s of {λx. inner})
   a` is a case that returns a function, applied once. Each branch runs once (no
   ω-scale) and `a` is aliased by `x`, so `a` is used exactly as many times as the
   branch uses `x`. Sound: `a` scaled by `x`'s usage, other captures counted once,
   and `a`'s OWN grade (the def's `:linear cap`) is still checked at its binding
   site — so a branch that drops (`a` → 0) or duplicates (`a` → ω) it is rejected
   there. The branch-λ grade is therefore ω; the sibling's real linearity is
   enforced via the convoy, not the branch binder.

Differential oracle `test/oracle/otp/ob1_branching*` mirrors Cure's `with r` against
Idris's native dependent `match` (which refines the linear sibling for free),
`rel=same` on accept + drop-reject + dup-reject. Behavioral test
`linear_sibling_refinement_test.exs`. Gates: Antigen 563/318-318, elab 1046, core
537, stdlib 49/0, replay 79.

Obligation (1) now has BOTH forms: the split `serve = reply(cap, handle(r))` and the
ergonomic branching handler. Restricted to a SINGLE sibling and the no-user-proof
case; multi-sibling and the `proof` clause keep the Eq-arrow path (reach-pinned).
