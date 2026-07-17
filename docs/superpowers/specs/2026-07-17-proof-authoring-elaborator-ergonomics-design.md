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

**Status.** OPEN. Workaround in use across `Std.Otp.*`. This is "roadblock #2" in the
OTP-metatheory directive.

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

**Status.** OPEN. Explicit-field carry is the current house style; flag each new use here.

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

## To verify (claims not yet isolated)

- Whether `_` is accepted as an explicit-argument placeholder in a call. A `coverage(_, s2)` call
  produced `:unknown_global`, but that may have been recursive-resolution noise, not `_` itself.
  Isolate before asserting.

---

## Maintenance

Append new entries as `E<n>` with the same fields. When an entry lands, mark it DONE with the
commit and leave it (history value). Cross-reference the Lean-shape matching spec for E1/E2 — a
full context-refinement implementation there closes most of this catalog at once.
