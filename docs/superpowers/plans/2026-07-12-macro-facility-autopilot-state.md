# AUTOPILOT STATE — Macro Facility Build (base + self-proving extension)

**Started:** 2026-07-12. **Branch:** `core-let-binder` (staying in the accumulating
stack — the macro work builds on the landed Effect/graded-binder/Std.Otp stack here;
deliberate deviation from autopilot's nested-worktree default, per
autopilot-worktree-preference). Cron-driven; this file is the durable resume point.

## Stage 0 — DONE (design approved, specs committed)
- Self-proving design APPROVED by operator; specs committed:
  - `docs/superpowers/specs/2026-07-11-self-proving-macros-design.md` (extension)
  - `docs/superpowers/specs/macros/2026-07-08-macro-facility-design.md` (base)
  - `docs/superpowers/specs/macros/2026-07-12-racket-syntax-parse-comparison.md`
  - `docs/superpowers/plans/2026-07-12-macro-facility-program.md` (SP decomposition)
  - `docs/superpowers/plans/2026-07-12-macro-facility-sp1-grounding.md` (parser map + architecture)

## The program: 6 sub-projects (run the autopilot chain per SP, in order)
SP1 minimal facility (container+grammar+Tiers1-2) → SP2 Tier3+typed errors+examples →
SP3 generative expansion proof → SP4 reflection API → SP5 behaviour/lift-module (Std.Otp
ceiling) → SP6 Tier5+DSLs. SP1→SP2 spine; SP3/4/5 fan out from SP2.

## Autopilot chain PER sub-project
Stage 2 write the SP plan (writing-plans) → Stage 3 plan review (Sonnet subagent,
recursive-skeptical-review) → Stage 4 TDD execute (Opus) → Stage 5 code review (Sonnet
subagent) → Stage 6 verify (full suite). Commit per stage/task. Stage 1 spec review is
DONE for the shared specs (self-reviewed); each SP plan still gets Stage 3.

## Locked decisions carried into every SP
- **TCB delta ZERO** — macro output is re-elaborated + kernel-checked; NO `lib/cure/core/*`
  changes. Any SP that thinks it needs one is mis-scoped → HALT.
- **User-facing syntax DEFERRED** (operator: easiest to change) — use the design's current
  notation as a placeholder; do not block on surface spelling.
- **Port syntax-parse's machinery** for error quality (comparison doc §4): failure-SET →
  maximal-by-progress → report(message,context,at,within). **Thread progress from SP1
  task 1** (retrofitting it later is painful).
- Self-proving obligations: SP2 (typed exhaustive Diagnosis incl. `fail C`, required
  examples) + SP3 (full generative expansion fuzz on every macro compile).
- Two-phase parse (pre-pass seeds `active_macros` from `use`+local defs) = SP1's
  architectural core (grounding doc). Soft-keyword `macro`; `{:macro_def,meta,rules}` AST.

## CURRENT POSITION
SP1, Stage 2 DONE for milestone 1 (macro-definition front-end): plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp1-plan.md` (`6f76a94`), tasks 1-3
with complete anchored code (soft-keyword `macro`, `syntax` rules, typed holes →
`{:macro_def, meta, rules}` progress-slotted AST). Parser anchors verified & recorded in
the plan's Global Constraints (Token/state/helpers, soft-keyword dispatch at
parser.ex:292-340, parse_fsm template at :3894).

Stage 3 DONE — plan hardened + committed `6dedd96` (4 passes, 2 clean). Reviewer caught
& fixed two CRITICAL defects and VERIFIED the corrected code for real (scratch-applied,
6/6 new tests pass, `test/cure/compiler/` suite = 625 passed, then reverted):
- `Parser.parse/2` returns the BARE node, never a list → tests use `node = parse!(...)`.
- `end` is a reserved keyword no container consumes; Cure containers close by DEDENT →
  the macro sources have NO trailing `end` (`macro Every\n`, not `macro Every\nend\n`).
- Token atoms `:lt`/`:gt`/`:colon` confirmed correct; all anchors verified exact.
Use the HARDENED plan (`6dedd96`) for execution — it is proven to work.

Stage 4 milestone-1 DONE — SP1 tasks 1-3 executed inline TDD (red→green per task),
committed `c381e7a` (container skeleton), `8f07931` (bare-keyword syntax rules),
`77cbd6d` (typed holes). `test/cure/compiler/macro_def_parse_test.exs` = 6 passed; full
`test/cure/compiler/` = 625 passed / 1 skipped (baseline, no regression). The
macro-definition front-end is live: `macro Name` → `syntax kw <hole: Kind> becomes tmpl`
→ `{:macro_def, [name,line,col], [%{kind: :syntax, keyword, segments: [{:lit,_}|{:hole,%{name,kind,line}}], template, progress: nil, line}]}`.

Stage 5 milestone-1 code review DONE — 7 passes (6 clean). Found + fixed ONE real defect:
`##` doc-comments (always `:doc_comment` tokens, not gated by preserve_comments) broke the
container — a doc-comment as first body line silently emptied the rule list; between rules
it threw spuriously. Fix `4295479`: `skip_macro_trivia/1` (newline + doc/line comments) at
every container-body skip point + 2 red tests. `test/cure/compiler/` = 627 passed;
`--warnings-as-errors` clean; macro non-breaking in all positions verified.

MILESTONE 1 (macro-definition front-end, SP1 tasks 1-3) is COMPLETE through Stage 5:
commits `c381e7a` `8f07931` `77cbd6d` `4295479`.

SP1 milestone 2 Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp1b-plan.md`. It scopes the milestone to
the **critical path to "a local macro expands"** (the observable spine), with T4/T7/T8/T9 as
noted subsequent increments:
- **Task 1 (T5) — two-phase parse:** `active_macros: %{keyword => [rule]}` on parser state;
  `parse/2` runs a harvest pass (parse once, keep only `{:macro_def}` nodes via
  `collect_macro_defs/1`) then an authoritative pass seeded with it. LOCAL macros only (`use`
  inert at parse time → imported grammars deferred to T9). Test pins no single-pass regression.
- **Task 2 (T6a) — zero-hole use-site expansion:** guarded `:identifier` dispatch
  (`is_map_key(state.active_macros, name)`) → `parse_macro_use/2` → `expand_rule/2`
  (`subst_holes/2` walks the template). `now` → `Clock.now()`.
- **Task 3 (T6b) — hole matching + substitution + progress:** `match_segments/4` walks
  `{:lit}`/`{:hole}` segments, binds holes via `parse_expr`, records progress (syntax-parse
  maximal-by-progress hook), substitutes. `every <t: Code>` → `Timer.repeat(t)`.

SP1 milestone 2 Stage 3 DONE — sp1b plan HARDENED + committed `e6883fe` (6 passes, 2
consecutive clean). Reviewer verified every claim against the REAL parser (ran `Parser.parse/2`
on live source) and caught 2 real defects + added coverage:
- **CRITICAL fixed:** Cure has NO `def` keyword (it's `fn`). The Task 2/3 fixtures `def f() = …`
  parse to a bare `{:variable,_,"def"}` + `{:assignment}`, never `{:function_def}`. All fixtures
  changed to `fn f() = …`; `find_fn_body` pinned to the CONFIRMED shape (no more asserted-then-
  verify hedge).
- **HIGH fixed:** the macro-use dispatch clause is checked FIRST in `parse_prefix/1`'s
  `case token.value do`, ahead of `sup`/`app`/`macro`/`with`/`assert_type`/`rewrite`. A local
  macro named `sup` would silently disable the supervisor container module-wide. Guarded with
  `@reserved_macro_keywords` (`name not in @reserved_macro_keywords`) + a red collision test.
- **Coverage added:** Task 3 shipped 3 behaviors (hole-bind, literal-match, literal-mismatch
  error) with only 1 named red test → added 2 more (two-literal-segment match; literal mismatch
  asserting `:macro_use_mismatch`), each verified genuinely red against baseline.
- Harvest-pass fragility (soft spot a) reviewed: judged acceptable for v1 (recovery surfaces the
  `{:macro_def}` nodes); constrain-def-before-use / structural-prescan is the noted enhancement.

Use the HARDENED plan (`e6883fe`) for execution — its code snippets were mechanically
syntax-checked (`Code.string_to_quoted!`) and the reserved-keyword guard is in the plan.

SP1 milestone 2 Stage 4 DONE — all three tasks executed inline TDD (red→green), committed:
- **T5 `d66bf57`** — `active_macros: %{}` on parser state; two-phase `parse/2` (harvest pass →
  `harvest_active_macros/1`/`collect_macro_defs/1` → authoritative pass). `test/cure/compiler/`
  628 passed.
- **T6a `0bd320f`** — guarded `:identifier` dispatch (`is_map_key(active_macros,name) and name
  not in @reserved_macro_keywords`) → `parse_macro_use/2` → `expand_rule/2`/`subst_holes/2`.
  `now` → `Clock.now()`. Reserved-keyword collision (`sup`) test proves the guard. 630 passed.
- **T6b `94c33a6`** — `match_segments/4` walks `{:lit}`/`{:hole}` segments, binds via
  `parse_expr`, records progress, `{:error,progress,state}` recovery emits `:macro_use_mismatch`.
  `every <t>` → `Timer.repeat(500)`; `say hello` literal match; `say goodbye` mismatch error.
  633 passed / 1 skipped, `mix compile --warnings-as-errors` clean.
- **Test-helper fix during execution (flag for reviewer):** the plan-provided `has_supervisor?/1`
  helper had a provably-wrong first clause — `{:container, meta, _}` matched the enclosing MODULE
  container and short-circuited to `false` without recursing into children (where the supervisor
  lived). The behavior under test (parser produces the supervisor despite the macro collision) was
  CORRECT — verified by raw-tree probe. Fixed the helper to check container_type AND recurse. This
  is a legitimate immutability exception (test helper wrong, not the impl); Stage-5 should confirm.
- **Wrong-directory hazard recorded:** `mix` MUST run from the worktree root
  (`.claude/worktrees/core-let-binder`), NOT the parent clone `/Users/ch/Develop/esp32-beam/cure-lang`
  — the parent lacks the macro code, so running there gives phantom "macro front-end regressed"
  failures. Never `cd` out of the worktree for a build.

SP1 milestone 2 Stage 5 DONE — Sonnet code review over the Stage-4 code diff (`754e8d0..94c33a6`),
converged 3 passes (2 clean). Found + fixed ONE genuine defect red-test-first:
- **`6e01715`** — `subst_holes/2` only recursed into a node's `children` (3rd tuple elem), never
  its `meta` (2nd elem). `match_arm` stores pattern/guard in META, so a hole referenced from a
  template's match-arm guard (`check <x> becomes match 1 { y when x -> 1, ... }`) survived
  expansion as a dangling `{:variable,_,"x"}`. Fix walks meta values too (`subst_holes_meta/2` +
  `subst_holes_meta_value/2`), scalar-safe. Red test `"a hole referenced inside a template
  match-arm's guard is substituted"` added.
- Reviewer cleared the other scrutiny points: harvest is order-independent module-wide by design
  (use-before-def works); reserved-keyword list exactly matches the 6 hard-coded soft-keyword
  clauses; greedy hole-then-literal either just-works or errors loudly (T4-deferred, not silent
  corruption); error-recovery arm has guaranteed forward progress (no infinite loop); the
  Stage-4 `has_supervisor?` helper fix confirmed legitimate.

SP1 milestone 2 Stage 6 DONE — **full `mix test` green: 4099 passed / 2 skipped, 3 doctests**,
159 expected immune responses, antigen shape-coverage 328/328 ✓. Parser change globally safe.

**MILESTONE 2 (local macro use-site expansion) COMPLETE** through review+verify: a locally-defined
macro now parses, and its use-site EXPANDS to substituted surface AST (zero-hole, single-hole, and
literal-segment forms), re-checked by the existing elaborator/kernel (TCB delta zero). Commits
`d66bf57` `0bd320f` `94c33a6` `6e01715`.

SP1 T8 Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1c-plan.md`.
**Scoping decision:** split the planned "T7+T8" round — this plan is **T8 alone** (the soundness
firewall, the DONE-criterion spine "expands to well-typed Core"); T7 (hygiene) is deferred to its
own plan `…-sp1d-plan.md` because it is a distinct red-green feature (gensym + capture-avoidance)
needing its own grounding. Keeps each plan a coherent testable unit.

T8 grounding is LIVE-PROBED, not assumed — ran `Cure.Elab.Program.elaborate/1` (`program.ex:16`,
returns `{:ok, Env}` / `{:error, term}`) on real macro programs. Because expansion is a PARSE-TIME
surface rewrite, expanded AST flows through the unchanged elaborator+kernel, and macro programs get
the IDENTICAL verdict to their hand-written equivalents:
- `zero`→`0` as Int ⇒ accept (== hand-written `fn f() -> Int = 0`).
- `inc <x>`→`x + 1` on Int param ⇒ accept.
- `bad`→`nonexistent_thing` ⇒ reject `:unknown_global` (== hand-written, identical term).
- `tt`→`true` as Int ⇒ reject `{:conversion_failure, {:data,:Bool,[],[]}, {:int_type}}` (== hand-written).
Error terms are position-free → exact `==`. T8 = a firewall test (`test/cure/elab/macro_expansion_
soundness_test.exs`) asserting verdict-equality, **zero production delta** (expansion already re-
elaborates). Honestly framed as characterization/firewall (green-from-green, like the milestone-2
Task-1 pin + `emit_hole_firewall_test`), with a red-first NEGATIVE CONTROL step proving the equality
has teeth. Flagged for the Stage-3 reviewer: validate the firewall-not-red-green TDD framing and that
verdict-equality can't pass trivially (accept-sense + reject-sense pins guard that).

SP1 T8 Stage 3 DONE — plan hardened + committed `2f878af` (4 passes, 2 clean). Reviewer verified
all four verdicts live and surfaced a CRITICAL scoping finding: `Program.elaborate/1` is the
DEPENDENT entry, but `cure build`/CLI (`Cure.Compiler.compile_string/2`) routes NON-dependent
programs (all four T8 examples classify non-dependent per `dependent?/1`) through the CLASSIC
`Types.Checker` + classic Codegen — so Task 1 alone doesn't firewall what `cure build` does today.
Reviewer honestly rescoped the plan + flagged it as a driver/operator decision (did NOT silently
patch).

**FORK RESOLVED (driver decision `36a3289`, prose per convention):** firewall BOTH entry points.
Live-probed that classic `compile_string` verdict-equality ALSO holds (line-stripped, all four
`equal=true`). Task 1 = permanent dependent firewall (the "well-typed Core" path the DONE criterion
names; survives classic rip-out). Task 2 = TRANSITIONAL classic firewall (delete when
classic-pipeline-deletion lands) giving `cure build` real protection now. Both test-only, zero
production risk.

SP1 T8 Stage 4 DONE — both firewalls executed, negative-control-proven teeth, then committed:
- **`3a7383d`** `test/cure/elab/macro_expansion_soundness_test.exs` — dependent firewall, 6 tests
  (4 verdict-equality + accept-sense + reject-sense). Negative control failed as predicted (`:accept`
  ≠ `{:reject, conversion_failure}`) then deleted.
- **`52b997c`** `test/cure/compiler/macro_expansion_classic_soundness_test.exs` — transitional classic
  firewall, 6 tests, line-stripped verdict-equality. Negative control failed then deleted.
- **ZERO production delta confirmed** (`git status` showed only the 2 new test files; no `lib/**`) —
  this IS the empirical proof of TCB-delta-zero: macro expansion re-elaborates on BOTH pipelines with
  no code change. Full `mix test` **4111 passed / 2 skipped**, antigen 328/328, seeds/corpus untouched.

SP1 T8 Stage 5 DONE — Sonnet code review over the T8 test diff (`36a3289..HEAD`, two files),
converged CLEAN (2 consecutive clean, zero findings, no commits). Reviewer EXERCISED not just read:
parsed each macro_src to confirm the expansion is textually faithful to the hand-written body (proved
`bad`→`nonexistent_thing` genuinely expands to `{:variable,_,"nonexistent_thing"}` — rejection driven
by the EXPANSION, not a coincidental both-sides parse failure); traced `strip/1` (no over/under-strip);
confirmed async-safety (`Program.elaborate` Process-local; `compile_string`'s `Cure.M.beam` write is a
pre-existing inert last-write-wins convention, nothing reads it back); ran an adversarial 5th case
(`inc true` vs `true + 1`) — verdicts matched both pipelines. 12/12 pass across seeds {0,1,42,999};
`test/cure/compiler`+`test/cure/elab` together = 1481 passed. Confidence high.

**SP1 T8 COMPLETE** (all stages): dependent firewall `3a7383d` + transitional classic firewall
`52b997c`, plan `99b8be6`/`2f878af`/`36a3289`. The DONE-criterion clause "expands to well-typed Core"
is now permanently guarded on both pipelines with the zero-production-delta proof of TCB-delta-zero.

SP1 T7 Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1d-plan.md`.
Grounded LIVE (not assumed): capture bug PROVEN — `addtmp <e> becomes let tmp = 100 in e + tmp` +
`fn f(tmp) = addtmp tmp` expands to `let tmp = 100 in tmp + tmp` where the hole-substituted param `tmp`
is CAPTURED by the template's `let tmp` (computes 100+100 regardless of arg). Parser facts probed:
`<fresh g>` tokenizes `:lt id("fresh") id("g") :gt` (`fresh` not reserved); template parsed via
`parse_expr` at `parser.ex:4120`; `parse_prefix/1` (now at `:381`) has no `:lt` case, bare `:lt`
hits default `{:unexpected_token}` at `:560`; infix `<` never reaches prefix (comparisons safe); the
`:lbrace` case `:545` is the window-lookahead idiom to mirror; expansion at `parse_macro_use`/
`expand_rule`/`subst_holes` `:195-221`.

**Scoping:** T7 = the EXPLICIT `<fresh Name>` primitive (design §5's named mechanism, deterministic
gensym `name$N` via a `fresh_counter` in parser state; freshen BEFORE hole-subst so use-site material
is never freshened; walks meta too, mirroring the T8-review `subst_holes` fix). AUTOMATIC full hygiene
(auto-rename every template binder, no annotation — §5 headline) needs template scope analysis → deferred
to **T7b** own plan. `<capture>` escape also deferred. Two tasks: T1 parse `<fresh Name>` → `{:fresh_name,
meta,name}`; T2 freshen at expansion (red = the capture repro with `<fresh g>`; green = binder gensym'd,
param `g` uncaptured). TCB delta ZERO.

SP1 T7 Stage 3 DONE — plan hardened + committed `5c903d3` (4 passes, 2 clean). Reviewer verified live
(patched parser.ex, ran, reverted) and caught 3 real TEST-CODE defects that would have caused false
failures at execution:
- **HIGH:** `find_fresh/1` helper couldn't reach the template — a macro rule is stored as a plain Elixir
  MAP (`%{template:...}`), not an AST tuple, so the generic tuple-recursion never descends. Test could
  never go green. Fixed: added `defp find_fresh(%{template: t}), do: find_fresh(t)` clause.
- **MEDIUM:** freshening walker didn't mirror the real `subst_holes_meta_value`'s `is_tuple`/`is_list`
  split — a `<fresh>` inside a raw-list meta value (e.g. `with`'s `:parent_patterns`) would leak
  unrewritten. Fixed: added `collect_fresh_names_value`/`apply_freshening_value`.
- **LOW:** vacuous `refute match?({:fresh_name,_,_}, assign)` (outer tuple can't match) → replaced with
  `refute find_fresh(body)`.
Verified SOUND (no finding): capture-bug AST shape is EXACTLY as planned (byte-for-byte); `<fresh g>`
tokenization; `parse_prefix` has no `:lt` case + infix `<` non-interference; parse paths; determinism
(harvest phase-1 never expands, `active_macros` defaults `%{}`); `expand_rule/2` has exactly one caller.
**Executor: trust the hardened plan `5c903d3` — its test code is now live-verified.** The real capture-repro
expanded AST (for Task-2 assertions): `{:block,_,[{:assignment,[let: true,...],[{:variable,_,"tmp"},
{:literal,_,100}]}, {:binary_op,[operator: :+,...],[{:variable,[line:4],"tmp"}, {:variable,[line:3],"tmp"}]}]}`.

SP1 T7 Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `af005b0`** — `:lt` case in `parse_prefix/1` recognizing the `<fresh Name>` window
  (`:lt id("fresh") id(name) :gt`) → `{:fresh_name, meta, name}`; else keeps `{:unexpected_token}`.
  `test/cure/compiler/` 641 passed.
- **T2 `cddf534`** — `fresh_counter` on state; `expand_rule/3` runs `freshen` BEFORE `subst_holes`;
  `freshen`/`collect_fresh_names(+_meta/_value)`/`apply_freshening(+_meta/_value)` mint one deterministic
  gensym `name$N` per distinct fresh name, rewrite markers + plain refs, walk children AND meta+list-meta.
  The capture repro is FIXED: `addg <e> becomes let <fresh g> = 100 in e + g` + `f(g) = addg g` expands so
  the binder is `g$0` (freshened), the param `g` stays uncaptured, template ref = `g$0`, no leftover marker.
  `test/cure/compiler/` 642 passed / 1 skipped; `macro_use_test` (milestone-2) still green (freshen is
  identity for non-`<fresh>` templates); `mix compile --warnings-as-errors` clean. TCB delta ZERO.

SP1 T7 Stage 5 DONE — Sonnet code review over the T7 diff (`5c903d3..HEAD`), converged CLEAN (5 passes,
2 consecutive clean, NO code changes). Core logic VERIFIED correct via live probes: two use-sites of the
same macro mint distinct `g$0`/`g$1`; harvest phase-1 never expands (counter untouched); repeated parse of
identical source → byte-identical ASTs (determinism); multiple fresh names sorted+independent (`a$0`,`b$1`);
all refs of one fresh name converge on one gensym; nested `addg(addg(1))` distinct inner/outer; two macros
same fresh spelling don't collide; freshening traversal mirrors `subst_holes` exactly (children+meta+list-meta);
non-`<fresh>` templates byte-identical; comparisons `a < b` unaffected. Full suite 4113 passed / 2 skipped,
antigen 328/328, warnings-clean.

**SP1 T7 COMPLETE** (`af005b0`+`cddf534`): `<fresh Name>` explicit hygiene primitive prevents ACCIDENTAL
capture (the proven `let tmp` capture bug is fixed). Two gaps found + characterized (NOT fixed — deferred to
**T7b** by design):
- **Fresh-name = hole-name silent-drop:** `syntax m <e> becomes let <fresh e> = 0 in e` called `m(99)`
  silently drops `99` — freshen rewrites the template `e`→`e$0` before `subst_holes` (keyed on "e") can bind
  it → `let e$0 = 0 in e$0`, no error. Genuinely silently wrong. T7b must add a fresh∩hole-name collision
  diagnostic (reject at parse, or freshen-after-subst ordering).
- **Backtick-gensym spoofing:** `` `g$0` `` (backtick ident accepts arbitrary chars incl `$`) as a use-site
  arg to a macro's FIRST invocation collides with minted `g$0` → real capture. Fundamental limit of STRING
  gensyms; robust fix = Racket-style uncopyable scope marks (T7b). Note: a NON-backtick user cannot produce
  `$`, so accidental capture IS prevented; only deliberate exact-gensym backtick-spelling defeats it. Connects
  to the general backtick-spoof trap ([[anonymous-adts-landed]]).
- Minor pre-existing (not T7): a stray `<fresh h>` OUTSIDE a template parses to an unhandled `{:fresh_name}`
  node and `cure compile` fails exit-1 with no diagnostic — general unrecognized-node-type gap, not T7-specific.

**SP1 SCOPE (re-confirmed against program-doc SP1 definition + GATE — do NOT skip to SP2):** SP1 explicitly
includes, beyond the done milestone1/2/T7/T8: **Tier-1 literal rules** (T4), **import scoping + same-keyword
conflict error** §7 (T9), **two-pass name resolution** §6, and the **default error-machinery FLOOR** §2 —
wrong-arity/unknown-category macro uses must produce a DIAGNOSTIC, not a raw parser error (currently
`:macro_use_mismatch` is raw-ish). SP1 GATE: a Tier-1 AND a Tier-2 macro compile+expand+kernel-check, bad
uses give a default-machinery diagnostic, full `mix test` green. So SP1 is NOT near-done; jumping to SP2
(self-proving typed errors) would skip real SP1 scope. Architecture note (T9 grounding, probed): cross-module
resolution (`import_source_env`/`module_slice_env`, program.ex:699/799) runs at ELABORATION, but macro
expansion is at PARSE time — so imported-macro grammars need the PARSER to locate+parse imported modules
(couples parser to import resolution). T9 is the hard architectural piece; sequence it after the tractable T4
+ error-floor.

**NEXT:** SP1 **T4** (Tier-1 literal rules + numeric-suffix lexer) Stage 2 — write
`docs/superpowers/plans/2026-07-12-macro-facility-sp1e-plan.md`. Ground the lexer change first: `lex_decimal`
has NO suffix support (`lexer.ex:795-826`); decide `500ms`→`{:literal}` with a unit tag vs a macro-hole
`literal` rule kind. Program-doc calls the Tier-1 exemplar a `units`-style macro. Then Stages 3-5. After T4:
the error-machinery floor (§2), then T9 (import scoping) + two-pass resolution (§6), then T7b (auto-hygiene +
the fresh∩hole + backtick-spoof gaps + `<capture>`). When ALL SP1 scope done+reviewed → SP1 Stage 6 full
verify, then SP2.

## DONE criterion (cancel cron + notify)
All 6 sub-projects implemented, code-reviewed, full `mix test` green, with an end-to-end
proof: a user-defined macro parses, expands, is generatively proven to expand to
well-typed Core, and its expansion runs. Then CronDelete + PushNotification.

## HALT protocol
Hard blocker or a review loop hitting pass 15 without convergence → update THIS file with
the blocker + what's needed, PushNotification, STOP. Never guess or accept an unconverged
artifact.
