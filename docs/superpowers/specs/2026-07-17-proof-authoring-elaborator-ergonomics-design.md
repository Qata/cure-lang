# Proof-authoring elaborator ergonomics — a living catalog

*Status: LIVING (append as encountered). Opened 2026-07-17 while dogfooding the OTP
metatheory in Cure (`Std.Otp.*`). Layer tags per `cure-porting`: **K** = trusted kernel
(`lib/cure/core/*`, HARD-STOP), **E** = elaborator (`lib/cure/elab/*`), **C** = codegen/erase,
**P** = parser.*

## Why this exists

Formalizing the OTP process algebra in Cure surfaced a recurring pattern: a lemma that is
*provable today* still costs the author an unnatural proof structure, an explicit-field
workaround, or a puzzling error, where a modest elaborator change would let them write the
obvious thing. None of these are soundness holes — the kernel stays honest — they are
**ergonomics**: the gap between the proof an author reaches for first and the proof Cure
currently accepts.

This catalog records each one with: the symptom, a minimal repro, the root cause + layer, the
current workaround, the proposed change, and whether it is soundness-neutral. It is the input
to prioritising elaborator work, and it feeds the partially-landed **Lean-shape matching**
programme (`2026-07-02-lean-shape-matching-design.md`) and the dependent-match surface
(`2026-07-02-dependent-match-surface-design.md`).

**Rule for future sessions:** when a proof only goes through via a structural trick, an
explicit-field carry, or after a confusing rejection that a smarter elaborator would avoid —
add an entry here. Do not silently absorb the tax.

---

## E1 — Refinement does not reach sibling context binders on `match` (the headline)

**Symptom.** Matching an indexed scrutinee refines the **motive** (goal type) but not the
**value of a sibling binder** that the matched constructor constrains. A later `match` on that
sibling then cannot prune impossible constructors, giving `{:reachable_impossible, C}` or
`{:missing_branch, C}`.

**Minimal repro** (from `Std.Otp.InferenceAdequacy` branching coverage). `SendSendK :
SendsIn(k,t) -> SendsIn(BSend(y,k), t)`, so matching `s` against `SendSendK` forces
`b = BSend(y,k)`:

```
fn coverage(b: Behaviour, {t: Tag}, s: SendsIn(b, t)) -> Member(t, infer(b)) = match s
  SendHere()    -> MemHere()
  SendSendK(s2) -> match b            # b SHOULD be refined to BSend(y,k) here
    BSend(y, k) -> MemThere(coverage(k, s2))
    BNil()      -> impossible          # -> {:reachable_impossible, BNil}
    ...
```

The nested `match b` sees `b : Behaviour` unrefined: the index equation `b = BSend(y,k)` learned
from matching `s` was applied to the goal but not substituted into the context, so `b`'s
impossibility analysis still admits `BNil`.

**Root cause + layer.** `elaborate_match` (E, with coverage support in K) solves the
scrutinee/constructor index unification and rewrites the **motive**, but does not apply the
resulting substitution to the **local context** (types/values of other binders). This is the
McBride "dependent pattern matching refines the whole context" step; Cure does the motive half
only. Confirmed by probes: sibling refinement DOES reach the motive (`infer(b)` reduces after a
single-constructor witness match — see E1-nongap below), but not a subsequent scrutinee position.

**Current workaround.** *Match the data before the evidence.* Scrutinize `b` first (binding
`l`/`r`/`k` by name), then the evidence `s` against an already-concrete `b`:

```
fn coverage(b: Behaviour, {t: Tag}, s: SendsIn(b, t)) -> Member(t, infer(b)) = match b
  BNil()      -> match s                       # SendsIn(BNil,t) uninhabited -> empty match OK
  BSend(y, k) -> match s
    SendHere()    -> MemHere()
    SendSendK(s2) -> MemThere(coverage(k, s2))
  BSeq(l, r)  -> match s
    SendSeqL(s2) -> member_append_left(coverage(l, s2))
    SendSeqR(s2) -> member_append_right(infer(l), coverage(r, s2))
```

This accepts today (verified 2026-07-17), zero TCB change. But the author must *know* to invert,
and the inversion is not always available (when the evidence, not the data, is what recursion
shrinks). It is also the deep reason the metatheory leans on **E2**'s explicit-field carries.

**Proposed change.** On `match`, apply the index-unification substitution to the whole context,
not just the motive — refining sibling binders whose value the matched constructor fixes, and
letting the coverage/impossibility checker use those refinements. Soundness-neutral: it reuses
the *same* unifier already trusted for the motive; it only widens where the result is applied.
Accepts strictly more programs. Overlaps directly with the Lean-shape matching spec's
context-refinement phase.

**Layer/risk.** E primary; the impossibility-pruning consumer may be K → HARD-STOP review +
Antigen antibody. Medium-high effort, high payoff (removes both the inversion tax and most E2
carries).

**Status.** ✅ FIXED. Branch substitutions now refine both context types and the
context's NbE values. Nested coverage observes a definitionally known constructor,
and the matching branch adds the constructor-field equations in the convoy direction
(outer existential → newly bound runtime field). The kernel independently performs
the same refinement and coverage check. `Std.Otp.InferenceAdequacy.coverage` now uses
the evidence-first formulation.

---

## E2 — Index existentials are not bound by name in patterns

**Symptom.** Matching an indexed constructor does not expose the constructor's index arguments
(existentials) as named term variables. A proof that needs the intermediate/left component of a
compound index cannot reach it.

**Repros (recurring across the metatheory).**
- `Runs(b, before)` / `RStep : Runs(b,before) -> StepAt(...) -> Runs(b,after)` — the recursive
  adequacy call needs `before`, an index existential, not surfaced by matching `RStep`.
- `LStep`/drain (`Std.Otp.ReplyConservation`) — the pending/answered counts are index
  existentials; the drain proof cannot name them from a bare `LThen` match.
- `BSeq(l,r)` left component `l` for `member_append_right(infer(l), …)`.

**Root cause + layer.** Same family as E1: pattern matching binds the constructor's *value*
fields but not its *index* arguments. E (`constructor_pattern` / motive machinery).

**Current workaround (two, both in the tree).**
1. *Make the index implicit and let inference recover it* — used for adequacy's config
   (`{c: Config}`), so the recursive call solves the intermediate config from a sibling's type.
   Works only when the index is *determined* by another argument (fails for `BSeq`'s `l`, which
   no sibling determines — hence E1's data-first inversion instead).
2. *Carry the needed component as an explicit constructor field* — `LAnswer` takes its counts
   `(p)(a)` explicitly so `LThen`'s match binds them (directive line 246). Pollutes the datatype
   with proof-only fields.

**Proposed change.** Allow naming index existentials in patterns (an `as`/named-index binder, or
surfacing them automatically when the constructor's index mentions a fresh variable). Largely
subsumed by E1 (context refinement makes the data-first re-match expose them cleanly); a
dedicated surface would remove the re-match step entirely.

**Layer/risk.** E. Medium. Soundness-neutral (binds already-present kernel data).

**Status.** ✅ FIXED for the E1-dependent use cases. Erased telescope slots now receive
distinct internal names (rather than every slot being `_erased`), and the branch
substitution transports their equations without making them computationally relevant.
Authors can request stable source names with the existing unforced named-implicit
pattern syntax; data re-matches expose relevant runtime fields naturally.

**Residual (seen 2026-07-17 in `Std.Otp.Conversation` / `Std.Otp.GenStatem`).** A
*relevant* index existential still can't be named in a proof body — e.g. `CRStep`'s
`t` (needed for the `MCons t …` congruence) or `SStep`'s split counts (needed for the
measure). The standing workaround is to add the value as an EXPLICIT constructor FIELD
(`CRStep : (t : Tag) -> …`, `SHandle : (p q : Nat) -> …`) so a data-match binds it, plus a
small congruence helper (`mcons_cong`) instead of an inline `reflexive` over the unnameable
index. Full fix = surface named-implicit *binders* on constructor patterns.

---

## E3 — Cross-module resolution of implicit-carrying stdlib functions (`:unknown_global`)

**Symptom.** `use Std.SomeMod; call a_fn_that_carries_implicits(...)` → `:unknown_global`.
Functions with only explicit args resolve fine across modules; adding an implicit parameter
breaks cross-module resolution.

**Repro.** `use Std.Otp.InferenceLaws; handles_mono(...)` (implicit-carrying) → `:unknown_global`.
Dodged in `otp_inference_laws_test` by making the test self-contained.

**Root cause + layer.** E-layer name resolution (`program.ex`) — the qualified/`use` import path
does not resolve the implicit-carrying def key. See memory
`cross-module-implicit-fn-resolution-bug`.

**Current workaround.** Keep such lemmas in a self-contained module, or inline. Blocks factoring
shared proof lemmas (e.g. `member_append_*`) into a reusable stdlib module.

**Proposed change.** Fix qualified-import resolution to carry implicit-argument defs. This is
**task #15** and the operator-designated next elaborator task after the OTP work.

**Layer/risk.** E. Completeness (not soundness). Medium.

**Status.** ✅ FIXED (`program.ex` `import_source_path`). Root cause was NOT implicits — it was
the module→file mapping: `String.downcase(Enum.join(segments, "_"))` mapped
`Std.Otp.InferenceLaws` to `otp_inferencelaws.cure`, but the file is `otp_inference_laws.cure`
(the convention snake_cases each segment). So `use` of ANY multi-word module
(`InferenceLaws`, `ReplyPreservation`, …) merged zero of its defs → `:unknown_global` on every
call, implicit or explicit. Fix snake_cases each segment (`Macro.underscore`) with the legacy
all-downcase form kept as a fallback. Regression tests in `cross_module_names_test.exs`.

---

## E4 — Partial application of an explicit-arg function does not codegen (codegen-adjacent)

**Symptom.** A partial application (e.g. a disproof `No(no_handles_nil(t))` where
`no_handles_nil : (Tag) -> (P) -> Empty`) **type-checks** but emits a call at the wrong arity, so
the loaded BEAM has `no_handles_nil/1 undefined`.

**Root cause + layer.** C (codegen/erase) — partial-app of an explicit-arg function is not
eta-expanded at emission. (Contrast E-layer partial-app of an *implicit*-carrying function, which
DOES eta-expand — see memory `branch-body-lambda-fallback-and-partialapp-hole`.)

**Current workaround.** Lambda-wrap: `No(fn(p) -> no_handles_nil(t, p))`. See memory
`partial-app-codegen-arity-gap`.

**Proposed change.** Eta-expand partial applications of explicit-arg functions at codegen, matching
the implicit-carrying path.

**Layer/risk.** C. Low-medium. Soundness-neutral (only affects emitted arity).

**Status.** ✅ FIXED (`emit.ex` `lower_app_spine`): the `{:global, name}` branch now detects
under-saturation (`length(args) < present_arity`) and eta-expands the missing parameters into
the curried 1-arg-fun ABI (`add(Z)` → `fun(V) -> add(Z, V) end`), instead of `Enum.split`
emitting a call at the supplied arity (`add/1`). Regression tests in
`partial_application_codegen_test.exs` (one/two-short + higher-order). The disproof lambda-wrap
workaround in `otp_inference.cure` is no longer needed.

---

## E5 — `##` comment lines between constructors in a `type` block are a syntax error

**Symptom.** A `## …` doc-comment line placed BETWEEN constructor declarations inside a
`type X indices (…)` block fails to parse (`syntax error` at each affected line). Comments are
only accepted before the `type` (or another top-level decl), not interleaved with its
constructors — so per-constructor documentation cannot sit next to the constructor it
describes; it must be collected into the block-leading comment.

**Repro.** In `Std.Otp.ExitSignal`, a `## normal + trapping: …` line before each `Step`
constructor errored; moving all of them into the comment above `type Step` fixed it.

**Root cause + layer.** P (lexer/parser) — the constructor-list grammar inside a `type` block
does not admit comment tokens between entries.

**Current workaround.** Put per-constructor prose in the block-leading `##` comment above the
`type`. (Costs locality: the reader cross-references names to descriptions.)

**Proposed change.** Allow `##` comment lines between constructors in a `type` block (skip them
in the constructor-list production).

**Layer/risk.** P. Low. Soundness-neutral (comments are non-semantic).

**Status.** ✅ FIXED (`parser.ex`): `parse_gadt_ctors` skips `:doc_comment`/`:line_comment`
between constructors, and the block entry uses `skip_newlines_and_comments` so a comment before
the first constructor (which lands before the block `:indent`) doesn't defeat block-open
detection. Regression tests in `parser_indexed_type_test.exs`; `Std.Otp.ExitSignal` documents
each constructor in place.

---

## E6 — nullary GADT constructor indices fixed only through a sibling's existential are unsolved

**Symptom.** Constructing a nullary GADT constructor whose indices are determined only via a
SIBLING argument's intermediate existential leaves `{:unsolved_metavariables, C}` at
elaboration — Cure rejects a term Idris accepts (a `cure_stricter` reach gap, an elaborator
incompleteness, not soundness).

**Minimal repro** (`Std.Otp.RestartIntensity`'s bounded-run liveness):

```
type FailRun indices (b1: Nat, p1: Phase, b2: Nat, p2: Phase)
  FRDone : FailRun(b, p, b, p)
  FRMore : Fail(b1, p1, bm, pm) -> FailRun(bm, pm, b2, p2) -> FailRun(b1, p1, b2, p2)
fn eventually_down(n: Nat) -> FailRun(n, Up, Z, Down) = match n
  Z()  -> FRMore(FShutdown(), FRDone())          # -> {:unsolved_metavariables, FRDone}
  S(k) -> FRMore(FRestart(), eventually_down(k))  # (and FRestart, symmetrically)
```

In `FRMore(FShutdown(), FRDone())`, `FRMore`'s intermediate index `(bm, pm)` is a metavar fixed
by `FShutdown : Fail(Z, Up, Z, Down)` (`bm=Z, pm=Down`); `FRDone`'s own indices must then unify
`FailRun(b,p,b,p) = FailRun(bm,pm,b2,p2)`. The solver does not propagate the sibling-derived
`bm/pm` into the nullary ctor's slots in time, so they stay unsolved. `FRDone` used where its
indices come DIRECTLY from the goal (e.g. `fn r() -> FailRun(Z,Down,Z,Down) = FRDone()`)
elaborates fine — the gap is specifically the sibling-existential routing.

**Root cause + layer.** E — metavariable solving order / propagation of a constructor
argument's intermediate existential index into a sibling nullary constructor. Same family as
E1/E2 (index existentials). Idris's unifier solves it.

**Current workaround.** None that keeps the natural proof. Ship the sub-theory that avoids the
routing (`Std.Otp.RestartIntensity` ships `Sup`/`Fail`/`on_fail`; the `eventually_down` run is a
blocked probe). Possible reformulations: give the constructors explicit relevant index args
(pollutes the datatype) — but note that pinning one ctor just moves the failure to the next
(pinning `FRDone` surfaced `FRestart`).

**Proposed change.** Propagate a constructor argument's solved intermediate existential indices
into sibling argument goals before finalizing metavariables (or a fixpoint solve pass).

**Layer/risk.** E. Medium. Soundness-neutral (accepts strictly more; the terms are well-typed —
Idris confirms).

**Status.** ✅ FIXED (`elaborator.ex` `check_ctor_args`), doing exactly what Idris2's
`TTImp.Elab.App.checkRestApp`/`checkRtoL` does: a present field whose instantiated type still
carries a metavariable is POSTPONED, its siblings are resolved first — solving that metavariable
— and it is then checked, iterated to a fixpoint so any dependency order works (earlier- OR
later-sibling-solved). A field that can be inferred in isolation solves the existential by
unify-back; one that cannot (a nullary constructor with its own implicit index) is deferred
until its type is concrete. The kernel re-checks the assembly, so it only widens what
elaborates. Full gate green (elab 1069, core 538, compiler exit 0). Regression tests in
`ctor_arg_deferral_test.exs`; the restart-intensity bounded-run liveness theorem now elaborates
AND codegens. NOTE: E1/E2 (the match side) are the SAME family; the postponement idea transfers
but the code path differs (this fixed the application side).

**Residual (seen 2026-07-17 repeatedly — `AStar0`, `RAStart`, `IRefl`, `SVHere`).** The fixpoint
solve handles a nullary indexed ctor whose index a SIBLING determines. It does NOT yet handle one
in DEEP nested argument position when the determining constraint lives only in the enclosing
call's expected type (e.g. `star_fold(APlusR(ATimes(…, AStar0())))`, `RAStep(RAStart(), …)`,
`CRStep(TB, SVHere(), CRDone())`): the inner nullary ctor's index is left `:unsolved_metavariables`
because the outer expected type isn't pushed inward far enough. Standing workaround: bind the
sub-term to a typed helper `fn h() -> T(concrete indices) = <ctor>` (the checking-mode annotation
pins the index), then use `h()` — same shape as `ra_start`. Full fix = push the checked type
through nested constructor arguments (bidirectional propagation into ctor-arg positions).

---

## Confirmed non-gaps (do NOT chase these)

Recorded so future sessions don't mistake them for gaps:

- **Sibling refinement into the motive WORKS.** A single-constructor indexed witness whose match
  fixes `b` *does* reduce `infer(b)` in the goal — verified with `SendHd : SendHd(BSend(t,k), t)`
  and a `Member(t, infer(b))` return. The gap (E1) is specifically the *context/scrutinee*
  position, not the motive.
- **Explicit relevant sibling `b` is refined for type computation.** `fn f(b, {t}, w: SendHd(b,t))
  -> Member(t, infer(b))` accepts. Making `b` explicit does not, by itself, reintroduce a
  refinement failure.
- **Empty `match` on an uninhabited indexed type WORKS.** `match s` with no clauses where
  `s : SendsIn(BNil, t)` (no constructor has a `BNil` head) is accepted and total — no explicit
  `impossible` needed.

## E7 — Explicit call-argument `_` was parsed as a global name

**Symptom.** `_` in a call such as `index(_, IsZ())` produced `:unknown_global`, even when a
later dependent argument uniquely determined the missing value.

**Root cause + layer.** E. The parser intentionally represents `_` as a variable-shaped AST,
but ordinary eager argument inference resolved it as a free global before the dependent
application solver could inspect the remaining Π telescope.

**Semantics.** `_` is a goal-directed placeholder only in a direct global call-argument slot.
The application solver creates a typed metavariable and allows later dependent arguments or a
concrete expected result to solve it. All placeholders must be solved before Core assembly, and the
kernel re-checks the resulting application. An unconstrained `_` is rejected; `_` outside a call
argument remains an ordinary error. Relevance is unchanged: a relevant runtime argument cannot
be reconstructed solely from an erased index. Thus `coverage(_, s2)` is valid only when `s2` (or
another constraint) determines a Core term that is legal at the present argument position; it
does not turn erased proof indices into runtime values.

**Status.** ✅ FIXED. Placeholder-bearing calls route directly to bidirectional Π-telescope
solving instead of first passing through eager free-name resolution. Regressions cover solving
from a later proof index, a runtime-carried dependent argument, and the expected result, plus
ambiguity rejection and the non-call scope boundary. The goal pre-pass retains the actual
placeholder meta rather than solving a disposable padding meta.

---

## E8 — Sequential-match refinement does not compose across independent scrutinees

**Symptom.** `deriv_sound` over the commutative-regex `Accepts` relation: after `match pat`
(binding `PTimes(a,b)`), a *separate* `match acc → APlusR(ar) → match ar → ATimes(m1,m2,…)`
whose constructor forces the index `m ≡ msadd(m1,m2)` does NOT update the goal — a subsequent
`rewrite msadd_assoc(m1,m2,…)` fails `:rewrite_no_match` because the goal still reads
`msadd(m, singleton(t))` with `m` unrefined. A one-probe control (`nest2`) with a *literal*
`Accepts(PPlus(PTimes(e,f),PZero), m)` scrutinee and NO outer `match pat` refines `m` correctly
through the same nested `APlusL → ATimes` chain. So the refinement machinery works; what fails is
composing a later scrutinee's index refinement into a goal a *prior, independent* match already
specialized.

**Root cause + layer.** E (same family as E1). Each `match` desugars to its own motive; the
motive built for `match acc` abstracts `acc`'s indices over the goal *as specialized by the
earlier `match pat`*, but the earlier match's branch goal is treated as fixed — the second
match's substitution (`m ↦ msadd(m1,m2)`) is scoped to its own elaboration and is not
back-propagated into the shared return type. Idris avoids this because a single clause matches
all patterns simultaneously (one unification problem), so every constructor's index equations are
in scope together.

**Semantics.** Nothing changes about what is provable — only whether it can be written without a
helper. A correct implementation would elaborate a `match` under the accumulated index
substitutions of enclosing matches (or, equivalently, adopt clause-simultaneous matching à la the
Lean-shape spec).

**Workaround (in use).** Helper-delegation: move the evidence match into a function whose `acc`
is a *parameter*, so no prior data-match has frozen the goal. `deriv_sound`'s `ds_times`/`ds_star`
match `acc` directly and mutually recurse with `deriv_sound`; the sum index then refines. Cost: an
extra top-level lemma per shape, and mutual recursion (which the kernel's termination cert accepts
here on structural descent).

**Status.** OPEN (worked around). Same fix as E1/E2 — full context-refinement / simultaneous
matching closes it.

---

## E9 — Stuck-index equation is not retained as a proof on GADT match

**Symptom.** Matching `acc : Accepts(PTimes(a,b), MkMS(Z,Z,Z))` as `ATimes(m1,m2,…)` (whose result
index is the stuck app `msadd(m1,m2)`) leaves `m1,m2` abstract with NO usable term witnessing
`msadd(m1,m2) = MkMS(Z,Z,Z)`. So `nullable_complete` / `deriv_complete` cannot invert the sum to
conclude `m1 = m2 = empty`. Matching `reflexive` for constructor injectivity (`MkMS(p,q,r) =
MkMS(Z,Z,Z) ⊢ p = Z`) gives `:conversion_failure` — injectivity is not derived from a `reflexive`
match either.

**Root cause + layer.** E/K boundary. When a constructor's index is a non-constructor (stuck
function application), the match introduces the unification constraint but neither (a) refines the
existentials nor (b) reflects the constraint as an `Equivalent` the branch body can eliminate.
Constructor injectivity of the equality type is likewise not exposed.

**Semantics.** The soundness-preserving fix is to reflect the residual index constraint as a
branch hypothesis `Equivalent(I, ctorIndex, scrutIndex)` (Agda/Idris `with`-style), and to provide
constructor injectivity for the identity type (a derived, TCB-neutral eliminator). Either unblocks
the inversion proofs.

**Workaround.** None clean — the completeness directions are deferred. (The SOUNDNESS directions
avoid inversion entirely and are proved.)

**Status.** OPEN. Distinct from E8: E8 is refinement not *composing*; E9 is the index equation not
*existing* as a term even for a single match.

---

## E10 — Higher-order function argument not reduced in a dependent index position

**Symptom.** Proving the monad laws for a free-monad `Eff(a)` with `bind(m, f)`: a proof whose
GOAL type mentions `bind(m, <function>)` fails to reduce the applied function. Concretely (a) a
LAMBDA in an `Equivalent` index — `Equivalent(Eff, bind(m, fn(y) -> Pure(y)), m)` — crashes
normalisation with `Eval.apply: … is not a function` and the bound `y` mis-resolved to a global;
(b) a NAMED function passed there — `bind(m, ret)` — yields `:branch_type` because `bind(Pure(x),
ret)` is not reduced through `ret` during conversion; (c) a PARTIAL application there —
`bind(m, kcomp(f, g))` — likewise does not reduce. First-order proofs are unaffected (the
value-less effect algebra was re-stated as a MONOID `(Eff, seq, ENil)` and its laws proved).

**Root cause + layer.** K (normaliser) + E. Reducing `bind` applied to a concrete continuation in
a *type/index* position requires β/δ-reduction of the applied function under the motive; the
kernel's conversion does not drive this for a lambda (whose closure mis-captures the binder here),
a δ-unfoldable name, or an under-applied global. In *term* position the same reductions work — it
is specifically the index/conversion path.

**Semantics.** No soundness impact; a completeness/expressivity gap. The fix is to normalise
applied functions (β for lambdas, δ for names, saturation for partial applications) inside
conversion when they occur in an index, and to fix the lambda-closure capture in that path.

**Workaround.** For value-less effects, use the first-order MONOID formulation (no continuation
function) — `Std.Otp.EffAlgebra` proves left/right identity + associativity of `seq`. The
value-returning free-monad `bind` and its three monad laws stay blocked on this.

**Status.** OPEN. Related to E4 (partial-app codegen) but distinct: E4 is codegen of a partial
application; E10 is *reduction* of an applied function during type conversion.

---

## E11 — Applied DEFINITION head in a type/index position not resolved to its exact key

**Symptom.** A proof annotation applying a function whose name is defined in MULTIPLE modules
(`plus`, in `Std.Nat`/`EffAlgebra`/`MailboxPattern`/…) fails to convert even when both sides reduce
to the same normal form: `h() -> Equivalent(Nat, plus(S(Z()),Z()), S(Z())) = reflexive(S(Z()))`
REJECTS. Not about nesting or "imported functions" in general (earlier two mischaracterizations):
UNIQUELY-named imported functions (`count_sends`, `seq`) reduce fine; a LOCAL `idn(idn(Z))` reduces
fine. It is specifically an AMBIGUOUS applied def head. In TERM position the same `plus(…)`
correctly reports `:ambiguous_name`; only in TYPE/index position did it silently degrade. Even the
QUALIFIED spelling `Std.Otp.EffAlgebra.plus(…)` degraded the same way.

**Root cause + layer.** E (elaborator, `declarations.ex` — NOT TCB). `idx_to_core`'s `{:variable,…}`
clause resolves via `resolve_index_name` (which handles ambiguity), but the `{:function_call,…}` →
`lower_applied_type_head` CATCH-ALL for an applied plain def did `Env.resolve_key(env, env.defs,
atom)`, which for an ambiguous bare name falls back to the bare atom → `{:global, :plus}`, which is
not a registry key, so `Env.get_def`/`certified?` fail and δ-unfold stays stuck → conversion can't
reduce it. Separately, the qualified head was only offered to `resolve_qualified(…, :type)` (wrong
namespace for a value/def), so it degraded to the bare tail and hit the same catch-all.

**Semantics.** No soundness impact; a resolution/conversion-completeness gap.

**Status.** ✅ FIXED (Stage 1) in `lower_applied_type_head` via new `applied_def_key/3`: a qualified
head resolves through the VALUE namespace to `Mod#name` (and then δ-unfolds); a bare uniquely-provided
name resolves to its key; a bare name provided by ≥2 modules is a clean `:ambiguous_name` (matching
term position) instead of a silent conversion failure. Regression: `applied_def_resolution_test.exs`;
full gate green (4600 passed, 318/318 Antigen). **Stage 2 (OPEN):** TYPE-DIRECTED tie-breaking so a
BARE ambiguous applied def is resolved by the argument/expected types (per the approved
`overloading-and-argument-labels-spec`) rather than requiring the qualified spelling — the principled
fix for the remaining bare case. Distinct from E10 (a function ARGUMENT not reduced in an index).

---

## Maintenance

Append new entries as `E<n>` with the same fields. When an entry lands, mark it DONE with the
commit and leave it (history value). Cross-reference the Lean-shape matching spec for E1/E2 — a
full context-refinement implementation there closes most of this catalog at once (E8 included).
