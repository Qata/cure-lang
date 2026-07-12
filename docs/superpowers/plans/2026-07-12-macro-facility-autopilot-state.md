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

SP1 T4 Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1e-plan.md`.
**Key grounding correction (probed live):** NO lexer change needed — `500ms` ALREADY tokenizes
`[integer: 500, identifier: "ms"]` (`500 ms` identical; whitespace dropped). So T4 is PARSER-ONLY (lower
risk than the "numeric-suffix lexer" I'd assumed). Design fork resolved: it's a `literal` RULE KIND (base
§111/§194 `literal <n: Number> ms becomes Duration.ms(n)`), not a lexer unit-tag. A `literal` rule = leading
number-hole + `{:lit, suffix}` segment (reuses `parse_rule_segments`), but dispatches on a NUMBER use-site
(not a keyword). Two tasks: T1 parse `literal` rules (add `"literal"` clause to `parse_macro_rules/2` :4184;
`parse_literal_rule` skips the keyword, `suffix = first lit after hole`); T2 harvest by suffix into new
`literal_macros` state map + dispatch in `parse_prefix` `:integer`/`:float` (:386) → `maybe_literal_macro`
→ `expand_literal_rule` (binds number to hole, reuses `match_segments`/`expand_rule` so `<fresh>`+hole-subst
+T8 firewall apply). Anchors verified: `parse_macro_rules` only knows `"syntax"` today; `harvest_active_macros`
now guarded to `:syntax`-only + sibling `harvest_literal_macros`. TCB delta ZERO.

SP1 T4 Stage 3 DONE — plan hardened + committed `8b2ab36` (5 passes, 2 clean). Reviewer fixed a stale
line-number citation (`:integer`/`:float` at `:466-470` not `:386-390`), added a `:float` dispatch test + a
non-empty-map regression (`500 + 3` with `ms` macro defined), and TRACED suffix-consumption live (consumed
exactly once by `match_segments`, never double).

SP1 T4 Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `8c217da`** — `"literal"` clause in `parse_macro_rules/2` + `parse_literal_rule/1`/`literal_suffix/1` →
  `%{kind: :literal, keyword: nil, segments: [hole, {:lit,suffix}], suffix, template}`. 643 passed.
- **T2 `dfcf315`** — `literal_macros` state map seeded in authoritative `parse/2`; `harvest_literal_macros/1`
  (by suffix) + `harvest_active_macros/1` guarded to `:syntax`; `:integer`/`:float` dispatch →
  `maybe_literal_macro` → `expand_literal_rule` (binds number to hole, reuses `match_segments`/`expand_rule`).
  `500ms`→`Duration.ms(500)`, `3.5s`→`Duration.s(3.5)`; bare numbers + `500 + 3` unaffected. 647 passed /
  1 skipped, warnings-clean. TCB delta ZERO.
- **BUG CAUGHT BY TDD (flag for Stage-5 reviewer):** the hardened plan's harvester code had a latent
  `BadArityError` — the multi-clause inner `Enum.reduce` reducer `fn %{...} = rule -> ... ; _ -> acc end`
  dropped the accumulator param (a reducer needs `(element, acc2)`) and referenced the outer `acc`. Elixir
  doesn't catch mismatched anon-fn arity at compile time; the red test surfaced it immediately. Fixed to
  `fn %{...} = rule, acc2 when guard -> Map.update(acc2,...) ; _rule, acc2 -> acc2 end` in BOTH harvesters.
  This would have broken ALL parsing (harvest runs every parse) had it shipped — the Stage-3 review missed it
  (valid-looking multi-clause code), Stage-4 TDD caught it. Stage-5 should confirm the fix + look for similar
  arity issues.

SP1 T4 Stage 5 DONE — Sonnet code review over the T4 diff (`8b2ab36..HEAD`), converged CLEAN (2 passes,
NO fixes). Verified LIVE against a byte-for-byte pre-diff comparison worktree (`8b2ab36` snapshot): hot-path
`:integer`/`:float` dispatch byte-identical for EOF/index/list/negative/float/empty-map cases (the `{1,2,3}`
tuple-literal failure is PRE-EXISTING, not a regression); arity fix correct in both harvesters (no similar
latent mistakes); suffix/keyword collision deterministic (`500foo`→literal, bare `foo`→syntax, no crash);
reserved-word suffix inert; token consumed exactly once, multi-segment ok; malformed nil-suffix rules skipped;
two-phase harvest seeds `literal_macros` on authoritative state only, deterministic; `<fresh>` in a literal
template threads distinct gensyms (`x$0`/`x$1`); existing `syntax` rules had `kind: :syntax` pre-diff so the
guard is safe by construction. Full suite 647 passed. High confidence. (Minor cosmetic non-finding: the
`in ["Duration.ms","ms"]` test alternative's `"ms"` branch is dead — always `"Duration.ms"`; left as-is.)

**SP1 T4 COMPLETE** (`8c217da`+`dfcf315`, plan `a2c6d10`/`8b2ab36`). Tier-1 `literal` units rule live:
`500ms`→`Duration.ms(500)`, `<fresh>`+T8-firewall apply.

**SP1 GATE STATUS** (program-doc): Tier-1 ✓ (T4) + Tier-2 ✓ (milestone-2 `syntax`) + expansions kernel-check ✓
(T8 firewall) — the ONE remaining GATE-CRITICAL piece is the **default error-machinery floor (§2)**:
"wrong-arity/unknown-category macro uses produce a (default-machinery) DIAGNOSTIC, not a raw parser error."
Currently a bad macro use emits raw `{:macro_use_mismatch, kw, :at_segment, progress, l, c}` /
`{:expected, :syntax_rule, …}` tuples — must become structured diagnostics with a MESSAGE, using the
syntax-parse machinery (failure-set → maximal-by-PROGRESS [already threaded from T6b] → report
message/context/at/within — see `macros/2026-07-12-racket-syntax-parse-comparison.md`). This is the SP1
FLOOR (default messages); SP2 adds the type-ENFORCED author-defined `Diagnosis`.

**OPERATOR DECISION (2026-07-12): Elm-style error rewrite — DON'T stage, PARK.** Operator asked whether to
stage the macro error work behind an Elm-style error-system rewrite. Decided NO: the existing renderer
(`Errors.format_error/2` + `format_diagnostic/5` at `errors.ex:1730` + `suggest/2`/`levenshtein` typo hints) is
already partway to Elm (structured `severity: category` / `--> file:line` hyperlink / `| message`). Every
diagnostic routes through the ONE `format_diagnostic`, so a future Elm rewrite (source snippets + carets +
regions) upgrades ALL errors — macro included — for free; building the floor on it now is forward-compatible,
not throwaway. A full Elm rewrite is cross-cutting (every error site), its own initiative — PARKED at
`docs/superpowers/specs/2026-07-12-elm-style-error-rendering-PARKED.md` (committed `82d64a8`), with a
forward-compat contract the floor obeys (route through the central renderer; message content in the
`format_error` clause).

SP1 §2 error-floor Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1f-plan.md`.
Grounded: the RAW tuples (fall to catch-all `errors.ex:374`) are `{:macro_use_mismatch, …}` (single emit site
`parse_macro_use/1` `parser.ex:232`, `rule` in scope) + `{:malformed_hole, …}` (`parser.ex:4358`);
`{:expected, :syntax_rule/:becomes}` already renders (`errors.ex:86`, not raw). Two tasks: T1 ENRICH
`:macro_use_mismatch` to `{…, keyword, expected, got, line, col}` (`expected` = `{:literal,w}`/`{:hole_kind,k}`/
`:nothing_more` via `Enum.at(rule.segments, progress)`) + add a friendly `format_error` clause (routes through
`format_diagnostic`; updates the T6b shape-assertion in `macro_use_test.exs` — legit shape evolution); T2 a
`:malformed_hole` clause explaining `<name: Kind>`. TCB delta ZERO.

SP1 §2 error-floor Stage 3 DONE — plan hardened + committed `2d9e7e9` (6 passes, 2 clean). Reviewer
live-verified the load-bearing facts: for `say goodbye` vs rule `say hello` the emitted tuple is
`{:macro_use_mismatch, "say", :at_segment, 0, 4, 16}` → `progress = 0`, `Enum.at(segments, 0) = {:lit,"hello"}`
(plan's indexing EXACT); catch-all `errors.ex:374` = `format_diagnostic("error","compilation error",file,0,
inspect(error))` so the raw tuple string literally contains `:macro_use_mismatch`/`:malformed_hole` (both
`refute` assertions genuinely red pre-fix). Two findings fixed: (a) `macro_expected_at/2`'s `{:hole_kind,k}`
+ `:nothing_more` branches are DEAD (a `{:hole,_}` segment never fails in `match_segments` — it unconditionally
parses+binds — so only `{:lit,w}` mismatch reaches the fn; documented so the implementer doesn't chase an
impossible test); (b) Architecture prose promised `suggest/2` hints neither clause uses → corrected to
"out of scope for this floor". `:macro_use_mismatch` confirmed SINGLE emit site; T6b shape-assertion the ONLY
test coupled to the old shape.

SP1 §2 error-floor Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `e926038`** — enriched `:macro_use_mismatch` emit (`{…, keyword, macro_expected_at(rule,progress),
  macro_got_desc(t), line, col}`) + `format_error` clause → "the `say` macro expected `hello` here, but found
  `goodbye`"; updated the T6b shape-assertion. `macro_expected_at/2`'s non-`{:lit}` branches kept (dead-but-total).
- **T2 `34fb3ab`** — `:malformed_hole` clause → "a macro hole is written `<name: Kind>` …". Both route through
  `format_diagnostic` (parked-Elm forward-compat contract honored). 649 parser tests, warnings-clean.
- **Execution wrinkle fixed:** placing `defp article/1` BETWEEN the new `format_error` clause and the catch-all
  split the `format_error/2` clause group → `--warnings-as-errors` "clauses not grouped". Moved `article/1`
  AFTER the catch-all (clauses contiguous). A reminder: non-adjacent same-name/arity `def` clauses warn.

**SP1 GATE MET** (pending Stage-5 review): Tier-1 ✓ (T4) + Tier-2 ✓ (`syntax`) + expansions kernel-check ✓
(T8 firewall) + default-machinery diagnostics ✓ (this floor). TCB delta ZERO throughout.

SP1 §2 error-floor Stage 5 DONE — Sonnet code review over the floor diff, converged (4 finding-passes +
2 clean). Found + fixed FOUR real `macro_got_desc/1` defects, all red-test-first (the "found X" desc
corrupting `format_diagnostic`'s single-line message): `1fe7ef8` structural tokens (newline/indent/dedent
splice raw values), `98d4957` `nil` keyword → empty backticks, `9846f65` `:char` → codepoint not spelling,
`f421887` ROOT CAUSE = no control-char sanitization → all descs now route through `escape_for_diagnostic/1`.
Plus 2 test-only hardening commits (`0a94a90` direct-tuple coverage of the dead-but-total `{:hole_kind}`/
`:nothing_more` render arms; `74c3a4b` dedent case via real parse). Verified: `macro_expected_at` reachability
claim correct (hole segments never fail in `match_segments`); T6b assertion matches the real tuple; clause
ordering + grouping clean; no other consumer of the old shape. 8 floor tests + all macro suites green,
warnings-clean, antigen untouched.

**OUT-OF-SCOPE FINDING (reviewer, pre-existing — fix before SP1 gate is honestly met):** `match_segments/4`'s
`{:lit, w}` clause `to_string(tok.value) == w` (T6b code, `parser.ex` ~line 190s) CRASHES
(`Protocol.UndefinedError`/`ArgumentError`) when a use-site token's value is a tuple/list — a `:regex` token
value is `{body, flags}`, a `:string_interpolation` value is a list of parts. So `say /foo/` or `say "x#{y}"`
at a macro mismatch THROWS instead of producing a diagnostic — worse than the raw error the gate forbids.
Small fix: guard the comparison so a non-binary token value simply doesn't match (fall to the `{:error,
progress}` mismatch path → the friendly diagnostic). Pre-dates the floor diff (old `:at_segment` code hit it
too); it's in T6b's `match_segments`, not the error-floor.

`match_segments` non-scalar-token crash FIXED `eb5c70c` (red→green): reproduced live — `say ~r/foo/`
(:regex value = `{body,flags}` tuple) and `say "hi #{name}"` (:string_interpolation value = list) CRASHED
`to_string/1` in BOTH the lit-match (`match_segments`) and the got-desc (`macro_got_desc_raw`). Fixed:
`lit_token_matches?/2` (only scalar binary/atom/number values compare; structured → no-match → mismatch path)
+ `macro_got_desc_raw` clauses naming :regex/:string_interpolation/any structured value. (Clause-grouping
warning hit again — moved `lit_token_matches?` after the `match_segments` group.) 657 parser tests, warnings-clean.

## ═══ SP1 COMPLETE ═══ (Stage 6 green: full `mix test` = 4128 passed / 2 skipped, 3 doctests, antigen 328/328)
SP1 (minimal facility, Tiers 1-2) gate MET end-to-end:
- **Tier-1 literal units** ✓ (T4 `8c217da`/`dfcf315`): `500ms`→`Duration.ms(500)`.
- **Tier-2 hygienic `syntax` templates** ✓ (milestone 1 front-end + milestone 2 use-site expansion: `c381e7a`
  `8f07931` `77cbd6d` `4295479` `d66bf57` `0bd320f` `94c33a6` `6e01715`).
- **`<fresh Name>` hygiene** ✓ (T7 `af005b0`/`cddf534`): capture-free template binders.
- **Expansions kernel-check** ✓ (T8 firewall `3a7383d`/`52b997c`): macro output re-elaborated identically to
  hand-written — TCB delta ZERO proven.
- **Default error-machinery floor** ✓ (§2 `e926038`/`34fb3ab` + review fixes `1fe7ef8`/`98d4957`/`9846f65`/
  `f421887` + crash fix `eb5c70c`): bad macro uses render friendly diagnostics, never raw tuples OR crashes.
- Two-phase parse (harvest local `macro` defs → `active_macros`/`literal_macros`) ✓. All TCB delta ZERO.

**Deferred SP1 "Includes" (NOT gate-blocking; post-gate enhancements):** T9 (import scoping §7 + two-pass
name resolution §6 — cross-module macros, the hard parser/import-resolution lift), T7b (automatic full
hygiene + the fresh∩hole & backtick-spoof gaps + `<capture>`). Parked: Elm-style error rendering (`82d64a8`).

## ═══ SP2 STARTED ═══ (self-proving headline; large → sliced)
SP2 = "Tier-3 + self-proving Mechanisms 1 & 3" decomposes into slices (SP1 done). Full SP2 scope:
**M1** exhaustive `explain` over derived+extensible `Diagnosis` (`missing_diagnosis`) [self-proving §3];
**M3** required per-rule `example … expands …` (`rule_unpinned` + example-mismatch) [§5]; **Tier-3** `computed
by fn(...)` total compile-time Cure + `check … else fail` + author `fail C(args)` [§3.4]. GATE (all slices):
the 3 macro-compile errors fire on red fixtures / absent on green; example expansions kernel-check; suite green.

Grounding done (read self-proving §3.1-§3.4 + §5 + program-doc SP2; probed tokenization): `explain` = soft-kw
identifier; `Duration =>` = `identifier`+`:fat_arrow`; `keyword "w"` = `identifier`+`string`. `Diagnosis` is
DERIVED from grammar: one point per typed hole (`{:hole_kind, Cat}`) + per literal (`{:keyword, w}`). Key design
decision RESOLVED: the obligation CHECKS run in a NEW frontend module `Cure.Compiler.MacroValidate` (TCB-zero),
NOT the parser — so SP1's explain-less test macros don't break (this slice does NOT wire the check into the
compile pipeline; wiring + pinning SP1 macros is a later slice).

SP2 slice-1 (M1 structural) Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp2a-plan.md`.
Two tasks: T1 parse `explain` blocks → `%{kind: :explain, clauses: [%{point, body}]}` entry in `{:macro_def}`
rules (harvest ignores non-syntax/literal kinds); T2 `MacroValidate.check_explain_exhaustive/1` derives structural
points, checks coverage, emits `{:missing_diagnosis, uncovered}` + a friendly `format_error` clause. TCB delta ZERO.

SP2 slice-1 Stage 3 DONE — plan hardened + committed `8c4ab17` (3 passes, 2 clean). Reviewer patched the
plan's code into the tree + ran its own tests, fixing 3 findings:
- **CRITICAL:** `derive_points` only walked `rule.segments`, but a `:syntax` rule's DISPATCH KEYWORD (`every`)
  lives in the separate `keyword` field, NOT segments (probed: `%{kind: :syntax, keyword: "every", segments:
  [hole: …]}` — zero `{:lit}` for `every`). So the headline example derived ZERO keyword points → the check
  would pass vacuously. Fixed `derive_points` to special-case `%{kind: :syntax, keyword: kw}` → `{:keyword, kw}`.
- `parse_explain_point/1` had no fallback → `CaseClauseError` crashed the whole parse on a malformed point
  (`=> "x"`). Added total fallback (`add_error {:expected, :explain_point, …}` + non-advancing recovery) + a red test.
- Added "Tests immutable once green" to Global Constraints (matched sibling plans).
- CONFIRMED SOUND (no change): the indented `explain`-body parse works — `:indent` → `parse_block` unwraps a
  single-statement body to the bare expression; the clause loop lands on the next point/dedent correctly.

SP2 slice-1 (M1 structural) Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `f3fb1f1`** — `parse_explain_block/1`/`parse_explain_clauses/2`/`parse_explain_point/1` (with the total
  malformed-point fallback → `{:expected, :explain_point, …}` not a crash); `explain` dispatch in
  `parse_macro_rules/2` → `%{kind: :explain, clauses: [%{point, body}]}` entry. 659 parser tests.
- **T2 `8166c25`** — `lib/cure/compiler/macro_validate.ex`: `check_explain_exhaustive/1` derives structural
  points (holes + literals + the `:syntax` rule KEYWORD field per the Stage-3 CRITICAL fix), checks coverage,
  emits `{:missing_diagnosis, uncovered}`; `format_error` clause + `describe_point/1` (after catch-all). The
  "no explain block" test confirms BOTH `{:hole_kind,"Duration"}` AND `{:keyword,"every"}` are reported missing
  — the keyword-field fix works. 662 parser tests, warnings-clean. TCB delta ZERO.

**M1 structural mechanism LIVE (unwired):** a macro whose `explain` omits a failure point →
`MacroValidate.check_explain_exhaustive` returns `{:missing_diagnosis, [...]}` rendering a friendly diagnostic.
Not yet invoked by the compile pipeline (SP1 macros have no `explain`) — the wiring slice adds that.

SP2 slice-1 Stage 5 DONE — Sonnet code review over the diff, converged CLEAN (3 passes, NO defects, no code
changes). Verified LIVE: multi-rule + literal-rule (`keyword: nil` correctly skips keyword point; suffix+hole
derived) + trailing-literal derivation all correct; dedup deterministic (identical output twice; shared
hole-kind → one point); spurious explain clause ignored (matches design §3.2 exhaustiveness-only intent);
`covered?/2` total (only 2 point shapes producible); **malformed-point recovery tested vs 8 hostile inputs
under a 5s timeout — NONE hung** (`parse_expr` always consumes ≥1 token → loop progresses to dedent/eof);
empty explain block clean; `:explain` entry skipped by both harvesters + doesn't break expansion (`say hello`
still expands). Full `mix test` 4133 passed / 2 skipped, antigen 328/328, warnings-clean. High confidence.

## ═══ SP2 slice 1 (M1 structural exhaustive-explain) COMPLETE ═══
`f3fb1f1` parse explain + `8166c25` `MacroValidate.check_explain_exhaustive/1` + `missing_diagnosis` render.
A macro that omits a failure-point description → structured `missing_diagnosis` diagnostic. TCB delta ZERO.
Standalone (unwired) by design; the wiring slice enforces it in real compiles.

SP2 slice-2a (M3 presence, `rule_unpinned`) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2b-plan.md`. **Split M3 into 2a (presence) + 2b
(expansion-equality), since the α-renaming comparator + mini-expansion is substantial.** Grounded (probed
tokenization + §5.1/§5.2): `example`/`expands` = soft-kw identifiers; the `example` line is INDENTED under the
`syntax` rule (attach point = `parse_macro_rule` after `parse_expr` template); `expands : <Type>` = type-only
pin. Slice 2a = 2 tasks: T1 parse `example <use-site> expands <expected>` sub-blocks → capture use-site as RAW
TOKENS (names the macro's own keyword, can't expand at def-parse) + expected AST `{:expansion,ast}`/`{:type,ast}`,
attach `examples: [...]` to the `:syntax` rule map; T2 `MacroValidate.check_rules_pinned/1` → `{:rule_unpinned,
[keyword]}` for syntax rules with no example + `format_error` clause. `:literal` rules exempt (design §5.1 says
"every syntax rule"). TCB delta ZERO, standalone (unwired).

SP2 slice-2a Stage 3 DONE — plan hardened + committed `9617d16` (3 passes, 2 clean). Reviewer LIVE-VERIFIED
the highest-risk item (patched Task-1 code into real parser.ex, inspected AST): the indented-example attach
works — after the template's `:newline` the next token is `:indent`(4), `skip_macro_trivia` stops at it, the
`:indent` branch parses the example + `expect_dedent` consumes the inner dedent, leaving `parse_macro_block`'s
own `expect_dedent` the outer one; a TWO-rule source (`a` w/ example + sibling `b`) parses BOTH in order (`b`
as normal sibling with `examples: []`, not swallowed). Same indent/consume/`expect_dedent` idiom as
`parse_macro_block`/`parse_explain_block`. Only fix: stale `errors.ex:398` citation → content-anchored (catch-all
is ~line 409-411). Confirmed `examples: []` key doesn't break existing tests (they use `%{kind: :syntax}`
pattern-match, not full-map equality); `collect_until_expands` terminates; `expands : Type` branch correct.

SP2 slice-2a (M3 presence) Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `b7836c3`** — `parse_rule_examples/1`/`parse_example_lines/2`/`parse_one_example/1`/`collect_until_expands/2`;
  `example <use-site> expands <expected>` sub-blocks attach `examples: [%{use_site: [tokens], expected:
  {:expansion,ast}|{:type,ast}, line}]` to the `:syntax` rule map. 665 parser tests (the new `examples: []` key
  broke nothing, as the reviewer predicted).
- **T2 `15c36fc`** — `MacroValidate.check_rules_pinned/1` → `{:rule_unpinned, [keyword]}` for unexampled syntax
  rules (mixed-macro test: only `b` reported); `format_error` clause. 668 parser tests, warnings-clean. TCB delta ZERO.
- (Wrinkle: a background formatter kept re-touching `parser.ex` timestamps triggering stale Edit-state errors;
  `git status` showed parser.ex clean vs HEAD so content was intact — resolved by re-reading before editing.)

**M3 presence LIVE (unwired):** a syntax rule with no `example` → `check_rules_pinned` returns
`{:rule_unpinned, [...]}` rendering a friendly diagnostic. Standalone, same as M1 — the wiring slice enforces it.

SP2 slice-2a Stage 5 DONE — Sonnet code review over the diff, converged CLEAN (6 passes, NO defects, no code
changes). Verified LIVE all 8 items: multiple examples + syntax/literal/explain siblings after an example block
parse correctly (no dedent-swallow); missing-`expands`/empty-use-site/dangling — no crash/hang; `expands :ok`
correctly captured as `{:expansion, atom}` NOT a type pin (lexer makes `:ok` an `:atom`); `expands : Effect(Unit)`/
`List(Int)` full-type captured; `check_rules_pinned` exempts `:literal`-only macros (design §5.1 syntax-only);
M1+M3 checks coexist on one macro; use-site expansion unaffected. 668 tests, warnings-clean. High confidence.
- **Noted (not a bug, future polish):** an `example` line indented under a `:literal` rule → cascade of
  `{:expected, :syntax_rule}` errors (pre-existing one-token recovery), not a clean "literal rules take no
  example" diagnostic and not a crash. Out of scope. Also `expands :Int` (colon+uppercase, no space) lexes as
  atom `:Int` not a type pin — pre-existing whitespace-sensitive lexer behavior.

## ═══ SP2 slice 2a (M3 presence, `rule_unpinned`) COMPLETE ═══
`b7836c3` parse examples + `15c36fc` `check_rules_pinned/1`. Two of SP2's 3 gate errors now have live (unwired)
checks: **M1 `missing_diagnosis`** ✅ + **M3 `rule_unpinned`** ✅. TCB delta ZERO.

## OPERATOR DESIGN DECISION (2026-07-12): SP3 generator architecture — `Generator` typeclass + middle-path engine
Full spec: `docs/superpowers/specs/2026-07-12-generator-typeclass-pbt-architecture.md`. Decided across a design
session: (1) a `Generator(a)` TYPECLASS with stdlib conformance + `deriving` = the user-facing PBT magic
(`forall` on any type, generator auto-resolved) — lives in Cure `Std.Gen`/`Std.Test`, RUNTIME, unaffected by
any SP3 engine choice. (2) **MIDDLE PATH (Hegel pattern), chosen "for now":** separate ENGINE (drive-loop +
shrink + example-DB) from DOMAIN (the one shared `Generator` typeclass). SP3's macro fuzzer = compile-time
Antigen (host engine) invoking the SAME Cure `Generator` instances to fill typed holes → assert each expansion
elaborates. User PBT = `Std.Test` at runtime. ONE generator system, two runners by phase. REJECTED: reimplement
Hypothesis-in-Cure (Hegel's warned-against waste) AND literal-Hegel external-Python-Hypothesis server (breaks
self-contained BEAM toolchain). (3) **Phase 2 (later, operator: "rewrite on top of a ported conjecture"):** port
Hypothesis's choice-sequence CONJECTURE model → internal/free composable shrinking for every conforming type
(incl. derived), + example-DB unified with Antigen's corpus/replay; re-base both runners; `Generator` interface
survives unchanged. Enabler = SP2 Tier-3 (run Cure gens at compile time) + SP4 reflection (Code-hole gen) —
already SP3's prereqs, no reorder. OPEN Qs to verify before the foundation slice: Antigen's current shrinking
model; can the host engine invoke a Cure `Generator` at compile time; how much `deriving` is built; `Gen(a)`
repr that survives the re-base. Committed as a spec (this firing).

SP2 slice-2b (M3 expansion-equality, `example_mismatch`) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2c-plan.md`. Grounded LIVE: expansion of `every 500` =
`{:function_call, [name: "Timer.repeat", line:2, col:50], [{:literal, [subtype: :integer, line:3,col:16], 500}]}`
vs standalone `Timer.repeat(500)` — differ ONLY in `:line`/`:col` (semantic meta name/subtype identical). So
the α-comparator = **strip :line/:col from all meta + collapse `<fresh>` gensym suffix (`x$0`→`x`), then `==`**.
Two tasks: T1 `Parser.expand_example/2` (public driver — seeds `active_macros`/`literal_macros` from the rules
via a synthetic `[{:macro_def,[],rules}]`, builds a `%Parser{}` state on `use_site_tokens ++ [eof]`, calls
`parse_expr(state,0)` → the same expansion a real use-site gets, nested literal/`<fresh>` included); T2
`MacroValidate.check_examples/1` + `normalize/1` (strip_pos + degensym, mirrors subst_holes meta walk) →
`{:example_mismatch, [%{keyword,expected,actual}]}` + render clause. Scope: `{:expansion,ast}` pins only;
`{:type,ast}` type-only pins (§5.2, needs `Program.elaborate`) DEFERRED. Honest limit noted: gensym-suffix
strip is a first-cut α, not capture-aware de Bruijn. TCB delta ZERO, unwired.

SP2 slice-2b Stage 3 DONE — plan hardened + committed `16e0c2a` (3 passes, 2 clean). Reviewer patched the code
into the tree + ran it, catching a CRITICAL `normalize/1` bug: the two-clause version only stripped `:line`/`:col`
from nodes whose 3rd element is a LIST — but `:literal` nodes carry a SCALAR value (`{:literal, [subtype,line,col],
500}`), so they fell to the catch-all UNCHANGED, positions un-stripped → `check_examples` would reject virtually
every correct example (`2/4` tests failed live). Fixed with a third `normalize/1` clause for scalar-valued nodes
(`{t, meta, value} when is_list(meta)`); re-verified `4/4` + `672 passed`. Also confirmed live: `expand_example`
genuinely drives expansion (`every 500`→`Timer.repeat(500)`; nested `every 500ms`→`Timer.repeat(Duration.ms(500))`);
`normalize` keeps name/subtype/scope (so `f(1)`≠`g(1)`) while dropping positions; `$` not a legal Cure ident char
(degensym can't false-positive); the `for`-comprehension is valid; no-example/`{:type}` rules skip cleanly.

SP2 slice-2b Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `e9acf58`** — `Parser.expand_example/2` (public): seeds `active_macros`/`literal_macros` from a synthetic
  `[{:macro_def,[],rules}]`, parses `use_site ++ [eof]` via `parse_expr` → the real expansion. 669 parser tests.
- **T2 `f76de41`** — `MacroValidate.check_examples/1` + `normalize/1` (3-clause, scalar-node fix) →
  `{:example_mismatch, [%{keyword,expected,actual}]}`; `format_error` clause. `every 500 expands Timer.repeat(500)`
  ✓, `…expands Timer.repeat(999)` → mismatch, position-modulo match ✓. 672 tests, warnings-clean. TCB delta ZERO.

**M3 FUNCTIONALLY COMPLETE (unwired):** `rule_unpinned` (2a) + `example_mismatch` (2b). SP2 now has live checks
for ALL THREE gate errors: `missing_diagnosis` (M1) + `rule_unpinned` + `example_mismatch` (M3).

SP2 slice-2b Stage 5 DONE — Sonnet code review over the diff, converged (6 passes; 1 finding-pass + 5 clean).
Found + fixed TWO real defects red-test-first:
- **CRITICAL `1fdc661`** — `<fresh>`-BINDER false mismatch: a `<fresh Name>` marker parses to `{:fresh_name,
  meta, name}` with NO `scope: :local` key (freshen reuses that meta when rewriting to `{:variable,meta,gensym}`),
  but a hand-written pin's identifier ALWAYS carries `scope: :local` — so `normalize` comparing full variable meta
  made every correctly-pinned `<fresh>`-as-binder example spuriously mismatch, defeating the headline `<fresh>`
  self-proving case. Fixed: `normalize` drops `:variable` meta ENTIRELY (α-equivalence for a reference = its
  degensym'd name alone).
- **`3cb7bd2`** — `expand_example` discarded the parser state, silently swallowing trailing use-site tokens (a
  typo'd extra word after the hole), so a garbage example could check `:ok`. Fixed: check `peek(state)` post-parse,
  wrap in a `{:example_use_site_not_fully_consumed,…}` sentinel when tokens remain.
- Confirmed sound: `normalize` handles match-arm-with-guard (meta-embedded ASTs stripped via `normalize_meta_value`);
  multi-example/multi-rule ordering; determinism; `{:type}` pins skip; independent from M1/M3-presence checks.
  674 passed, warnings-clean, antigen untouched. High confidence.

## ═══ SP2 slice 2b (M3 expansion-equality, `example_mismatch`) COMPLETE ═══
`e9acf58` `expand_example` + `f76de41` `check_examples`/`normalize` + review fixes `1fdc661`/`3cb7bd2`.
**M3 COMPLETE** (`rule_unpinned` presence + `example_mismatch` equality). SP2 now has live (unwired) checks for
ALL THREE gate errors: `missing_diagnosis` (M1) ✅ + `rule_unpinned` + `example_mismatch` (M3) ✅. TCB delta ZERO.

**SEQUENCING CORRECTION (this firing, grounded):** the planned standalone "slice 2c = example kernel-check +
`{:type}` pins" is FOLDED INTO THE WIRING SLICE instead. Probed live: a self-contained expansion (`x + x`)
elaborates OK via `Program.elaborate`, but a real example's expansion referencing the macro's target functions
(`Timer.repeat(500)`) fails `:unknown_global` in isolation — the macro's IMPORT CONTEXT isn't in scope. So a
standalone example-kernel-check would false-reject nearly every real macro; kernel-checking examples needs the
elaborate-in-module-env machinery the wiring slice builds anyway. → next = **Tier-3** (independent, headline).

SP2 Tier-3 slice 1 (parse `computed by`) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2d-plan.md`. Tier-3 (`computed by` = expansion COMPUTED by a
compile-time Cure elab fn over quoted input, vs `becomes`'s template subst — design §3, tier row 3) decomposes:
**slice 1 (this) parse `computed by <fn>`** → `%{kind: :computed, keyword, segments, elab, examples}` (NOT
harvested → inert until execution); then **quoted-AST `Syntax` value model** (§3, `quote`/`$()`); then
**compile-time elab EXECUTION** (quote input → run elab staged-on-host → splice output; K3 firewall re-checks
output, TCB-zero — the big one); then **`check … else fail C`** (§3.4, ties to M1); then computed-rule example
checks; then the WIRING slice. Grounded: `computed by build_it` = 3 identifiers; `parse_macro_rule` branches on
verb after `parse_rule_segments`; `:computed` kind excluded by all harvest/MacroValidate filters (auto-inert).
One task: split the verb branch → `parse_becomes_rule`/`parse_computed_rule`. TCB delta ZERO.

SP2 Tier-3 slice-1 Stage 3 DONE — plan hardened + committed `3c3fed7` (5 passes, 2+ clean). Reviewer patched
the Task-1 code into a scratch build + RAN it, catching a CRITICAL bug the plan missed: `parse_rule_segments/2`
swallows `computed`/`by` as `{:lit,…}` SEGMENTS before the verb branch runs (its stop clause matched only
`"becomes"`), so the `%Token{value: "computed"}` branch NEVER fired — the plan's own tests 1+3 failed live
(`{:expected,:becomes,:got,:newline,…}`). FIX folded in: extend `parse_rule_segments/2` stop-word to
`v in ["becomes","computed"]` (shared helper; `parse_literal_rule` never uses `computed` so safe). With it,
all 3 tests pass + `test/cure/compiler/` 677 + soundness 6, zero regressions. Also verified: `parse_expr(state,0)`
captures the elab ref without over-consuming (bare + dotted + example-after + last-rule); `:computed` inert
(harvest/MacroValidate all exclude it); `by`-missing recovers cleanly; example sub-blocks attach.

SP2 Tier-3 slice-1 Stage 4 DONE — Task 1 (only task) executed inline TDD (red→green), committed **`ce62b17`**:
`parse_macro_rule/1` splits the tier verb after `parse_rule_segments` → `parse_computed_rule/4` (new,
`%{kind: :computed, keyword, segments, elab, examples}`) / `parse_becomes_rule/4` (extracted, unchanged);
`parse_rule_segments/2` stop-word extended to `v in ["becomes","computed"]` (the load-bearing fix). `computed by
build_it` → `:computed` rule capturing `{:variable,_,"build_it"}` elab; `:computed` inert at use-sites (parses
as bare var, not harvested); `becomes` rules byte-identical. 677 parser tests / 1 skipped, warnings-clean. TCB
delta ZERO. Parse-only — a computed macro can't EXPAND yet (execution is a later slice).

SP2 Tier-3 slice-1 Stage 5 DONE — Sonnet code review over the diff, converged (4 passes, high confidence). One
minor finding: the new `computed` reserved tier verb means a `literal`/`syntax` rule can no longer match the
literal word `computed` as a token (exact parity with the pre-existing `becomes` restriction; nothing in-tree
relies on it) → doc-only comment `a23fb70`. Verified SOUND via real probes: `becomes`-extraction byte-identical
(zero-hole/hole+lit/missing-becomes); `:computed` inert + excluded by ALL harvest/MacroValidate filters (probed
against a real `:computed`+unpinned-`:syntax` macro — no cross-contamination); malformed `computed`/`by`/EOF
recover cleanly; `parse_expr` elab-capture no over-consume. 677 tests / 58 macro tests, warnings-clean, antigen
untouched.

## ═══ SP2 Tier-3 slice 1 (parse `computed by`) COMPLETE ═══
`ce62b17` (verb-branch split + segment stop-word) + `a23fb70` (doc). Tier-3 front-end live: `syntax … computed
by <fn>` → `%{kind: :computed, elab}`, inert until execution. TCB delta ZERO.

SP2 Tier-3 EXECUTION ARCHITECTURE GROUNDED (this firing) — design note committed:
`docs/superpowers/specs/2026-07-12-tier3-computed-by-execution-design.md`. Decisions (driver, revisable):
- **A: execute by ELABORATE + NORMALISE, not compile-and-load.** Elaborate the elab ref → apply to the quoted
  input → `Cure.Core.Normalise.whnf`/normalise → the normal form IS the expansion. Reuses the trusted normaliser
  (verified callable), Cure-native, terminates (elabs are total), TCB-ZERO (normaliser unchanged; output re-elaborated).
- **B: GENERIC `Std.Syntax` value FIRST**; typed per-category derived records (§3 ideal) DEFERRED as ergonomic
  sugar. `Syntax = Node(tag, children) | Leaf(tag, value)` reflecting the parser `{tag,meta,children}` node; a
  `to_syntax`/`from_syntax` reflection bridge (Elixir) round-trips (positions can drop — K3 re-elaborates output).
- **C: `:computed` expands at ELABORATION time, NOT parse time** (needs elaborator+normaliser, absent at parse).
  Parser harvests `:computed` + emits a deferred `{:computed_use, meta, [elab, input_syntax]}` node; a compile-time
  expansion PASS in `lib/cure/elab/*` (untrusted → TCB-zero) walks + expands them. Phase distinction from Tier-1/2.
Probed: normaliser `whnf` callable; NO existing Syntax/quote/staging infra (greenfield); elaborator touch OK (untrusted).

SP2 Tier-3 slice-2 (`Std.Syntax` value + reflection bridge) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2e-plan.md`. Grounded live (found + corrected a design flaw):
meta is LOAD-BEARING (node names/operators/subtypes live in meta, not just tag/children) → `Syntax` must carry an
`attrs` field, else reflection loses function names. ADT: `Syntax = Node(Atom, List(Attr), List(Syntax)) |
Leaf(Atom, List(Attr), SynLit)`, `Attr = KV(Atom, SynLit)`, `SynLit = SInt|SFloat|SStr|SBool|SAtom|SOpaque`
(exotic regex/interp `third` → SOpaque, round-trips shape-only). Template = `Std.Json` `type Value` (nested
positivity proven). Two tasks: T1 `lib/std/syntax.cure` (elaborates-test mirrors `json_elaborates_test`); T2
`Cure.Compiler.MacroSyntax.to_syntax`/`from_syntax` Elixir bridge over a mirror repr, lossless round-trip
(up to line/col). TCB delta ZERO. NO execution (slice 3).

**OPERATOR STEER (2026-07-12) — elab-facing reflection API = TYPED derived record, NOT stringly `field`.**
Operator asked: parameterise `Syntax` over the definition so an elab writes `a.name` (typed) not
`a.field("name")`. YES — that's design §3's typed per-category derived records. From a rule's holes, synthesise
`rec RuleSyntax { <hole>: Syntax(<Kind>), … }` (`...` group → `List` of sub-record), thread as the elab's param
type → `a.name` compile-checked, self-documenting. The generic `Syntax` VALUE (slice 2) is the SUBSTRATE a typed
field holds underneath → slice 2 UNCHANGED + un-wasted; what's rejected is shipping a generic `field` accessor as
the elab API. Recorded in the Tier-3 execution design note (Decision B + slice 6, elevated to "land with/right
after execution"). Type-derivation-from-grammar = the new machinery (leans on landed dependent records).

SP2 Tier-3 slice-2 Stage 3 DONE — plan hardened + committed `ae0fa62` (4 passes, 2 clean, high confidence).
Reviewer patched the exact code into scratch + RAN it, fixing 3 grounding errors: (1) CRITICAL — the regex test
asserted tag `:regex`, but `~r/foo/` parses to `{:literal, [subtype: :regex], {body,flags}}` (tag `:literal`);
test fixed to `{:syn_leaf, :literal, attrs, :s_opaque}` + `{:subtype,{:s_atom,:regex}}` attr. (2) `@group(:syntax)`
isn't a recognized Preload group → `@group(:core)` (like sigma/proof). (3) stale `strip_pos/1`→`strip/1` xref.
VERIFIED LIVE: `Std.Syntax` elaborates `{:ok}` with just `use Std.String` (nested `List(Syntax)` positivity fine,
forward refs fine, `SOpaque` nullary ctor fine); round-trip preserves function NAMES + attr key ORDER (strip==
non-vacuous); `:string_interpolation` recurses cleanly (parts are real nodes, no crash). 1021 tests pass.

SP2 Tier-3 slice-2 Stage 4 DONE — executed inline on Opus, strict red→green, 2 tasks committed (ghost author,
explicit pathspec, mix from worktree root):
- Task 1 `f66db9f` — `lib/std/syntax.cure` (`Syntax`/`Attr`/`SynLit` ADT, `@group(:core)`, `use Std.String`) +
  `test/cure/stdlib/syntax_elaborates_test.exs`. Red (no file) → green; stdlib suite 340 pass.
- Task 2 `979fb36` — `lib/cure/compiler/macro_syntax.ex` (`to_syntax`/`from_syntax` mirror-repr bridge) +
  `test/cure/compiler/macro_syntax_test.exs` (3 tests: attr-preserving to_syntax, lossless round-trip over 7
  exprs, exotic regex-tuple → `:s_opaque`). Re-probed all parser shapes LIVE before writing (tests immutable):
  `g(1,x)`→`{:function_call,[name:"g",…],[…]}`, `~r/foo/`→`{:literal,[subtype: :regex,…],{"foo",""}}`,
  `x+2`→`{:binary_op,[operator: :+,…],…}`, `:ok`→`{:literal,[subtype: :symbol],:ok}`. Red → green;
  compiler+stdlib regression 1021 pass / 1 skip; `mix compile --warnings-as-errors` clean (vector.cure `.cure`
  warnings pre-existing, not Elixir).

SP2 Tier-3 slice-2 Stage 5 code review DONE — Sonnet subagent converged after 7 passes (4 consecutive clean) over
diff `2faf559..HEAD`, committed `6eaf70d` (ghost author, explicit pathspec). Found + red-tested + fixed 2 real
defects: (A) composite-meta blind spot — `synlit/1` collapsed list/map/AST-valued meta (binary-segment `size`/`unit`,
selective-`use` item lists, an interface's `defaults` table) to `:s_opaque`; fixed by adding `{:s_list,_}`,
`{:s_syntax,_}`, `{:s_map,_}` variants + `SList`/`SSyntax`/`SMap`/`SynPair` ctors on the ADT. (B) `to_syntax/1`
raised `FunctionClauseError` on non-3-tuple parser output (`impossible` arm body `nil`, 4-tuple `named_implicit_pat`);
fixed by a total `{:syn_raw,_}` catch-all + `Raw` ctor (reflect opaquely, matching regex precedent). Stale moduledoc
fixed. All 9 tests green; **Stage 6 gate run by the reviewer: `mix test test/cure/compiler/ test/cure/stdlib/` =
1026 passed / 1 skip (pre-existing)**. NO seeds/corpus noise. Out-of-scope note (NOT fixed, pre-existing, flagged
for later): parser.ex's own `subst_holes_meta_value`/`collect_fresh_names_value` Tier-1 hole walkers have the same
map-valued-meta blind spot if ever fed one.

## ═══ SP2 Tier-3 slice 2 (`Std.Syntax` value + reflection bridge) COMPLETE ═══ (Stages 2–6 done; `6eaf70d`)
Reflection substrate live: `lib/std/syntax.cure` (`Syntax`/`Attr`/`SynLit` ADT, now incl. `Raw`/`SList`/`SSyntax`/
`SMap`/`SynPair`) + `lib/cure/compiler/macro_syntax.ex` (`to_syntax`/`from_syntax`, total + lossless up to line/col).
TCB delta ZERO. This is the VALUE a typed derived field holds underneath (operator steer, `a.name`) — NOT wasted.

SP2 Tier-3 slice 3 Stage 2–6 DONE — plan committed `4ba6189`; implementation committed in phases:
- **`57c3a00`** — parser harvests `:computed` rules and emits deferred
  `{:computed_use, meta, [elab_ref, {:macro_input, meta, ordered_hole_inputs}]}` nodes. Parser tests cover
  zero-hole and hole-bearing rules; the parse-time harvest never executes an elab.
- **`7fa0a51`** — `MacroSyntax.to_core/1` + `from_core/1` encode/decode the complete generic `Std.Syntax`
  mirror (constructors, lists, strings, nested syntax, maps, opaque values).
- **`45b4157`** — `Cure.Elab.MacroExpand` elaborates the elab reference, kernel-infers the application,
  normalizes it through the existing trusted normalizer, decodes the result, and recursively splices it before
  ordinary body elaboration. Function bodies containing computed uses are ordered after plain bodies so a
  referenced total elab is checked/certified before execution. Structured error formatting and end-to-end
  tests cover valid zero/hole inputs and invalid output.
- **`20e8880`** — review fix: recursively decode `Node` children from Core instead of only decoding the list
  spine. Scoped compiler/elab/stdlib gate: **1874 passed / 2 skipped**.
- Full gate: **`mix test` = 4165 passed (3 doctests) / 2 skipped**, 151 expected immune responses,
  Antigen shape coverage **328/328**, no seed/corpus noise, `mix compile --warnings-as-errors` clean.

**NEXT (SP2 continues):** `check … else fail C` + computed-rule example execution, then the MacroValidate
wiring slice. When ALL SP2 done → SP2 COMPLETE → **SP3 (read the SP3 GROUNDING section below FIRST)**.
Deferred post-gate SP1: T9, T7b.

## ═══ SP2 Tier-3 typed derived records (Stages 2–6) COMPLETE ═══
Plan `docs/superpowers/plans/2026-07-12-macro-facility-sp2g-plan.md` committed as `769f124`.
The typed-record implementation is complete in three committed phases:
- **`4db5ca9`** — parser metadata records `syntax_type` (`MkSyntax`) and ordered unique
  `syntax_fields` for each computed rule; `Program.declarations/1` synthesizes the ordinary
  `rec MkSyntax` declaration with each field typed as generic `Syntax`.
- **`c3f2393`** — `MacroSyntax.to_core_record/2` encodes the reflected macro-input children as
  the generated record constructor, with direct empty/populated Core-constructor tests.
- **`a8e4588`** — `MacroExpand` supplies the generated record to typed computed elabs, runs the
  existing Core type/infer/normalize/decode firewall, and retains a generic-`Syntax` fallback for
  existing computed elabs. End-to-end tests cover `a.x` projection, expansion back to the use-site
  AST, and `unknown_field` rejection.

This slice deliberately keeps fields at `Syntax` rather than category-indexed types, and does not
implement repeated groups, quote syntax, `check … else fail C`, computed-rule example execution, or
MacroValidate wiring. TCB delta remains ZERO: no `lib/cure/core/*` changes.

Verification after the slice: `mix test test/cure/compiler/` = 692 passed / 1 skipped;
`mix test test/cure/elab/` = 847 passed / 1 skipped; `mix test test/cure/stdlib/` = 340 passed;
`mix compile --warnings-as-errors` passed; full `mix test` = 4170 passed (3 doctests) / 2 skipped;
Antigen shape coverage 328/328; worktree clean.

## ═══ SP3 GROUNDING — READ THIS WHOLE SECTION BEFORE TOUCHING SP3 ═══
(Written 2026-07-12 by the prior agent with full machinery probed live, for a fresh/less-context
agent. Every path, module, and function name below was verified against the tree on this date. Re-verify
line numbers before editing — they drift — but the module + function NAMES are load-bearing and correct.)

### SP3 mission (one sentence)
Make **every macro compile run a full Antigen-style fuzz of its own expansion**: generate a statistically
thorough sample of the DSL programs the macro's grammar accepts (by filling each typed hole with a generated
well-typed Core term of that hole's type), expand each, kernel-check the expansion, and **fail the MACRO's
compile** (with a shrunk counterexample) if any valid parse expands to ill-typed Core. Spec = self-proving
design **§4** (`docs/superpowers/specs/2026-07-11-self-proving-macros-design.md`, lines 174–241) — read §4.1–§4.5
verbatim; program-doc SP3 (`…-program.md`, "### SP3"). This is the **self-proving headline** and the clause of
the DONE criterion that reads "generatively proven to expand to well-typed Core." SP3 is the ONLY sub-project
that closes that clause — SP4/SP5/SP6 do not.

### Layer & TCB posture (NON-NEGOTIABLE)
SP3 is an **A + E/P-layer feature (untrusted): Antigen engine (`lib/antigen/*`) + the macro compile path
(`lib/cure/compiler/*`) + re-elaboration via the elaborator (`lib/cure/elab/*`).** TCB delta MUST be ZERO — do
NOT touch `lib/cure/core/*`. Soundness argument (spec §4.3): the generator emits well-typed Core, we assemble it
through the grammar, expand, and hand the expansion to the SAME trusted kernel checker that guards every other
program. A generator bug or a false "valid parse" can only make a macro **wrongly fail to compile** (a rejected,
not an unsound, program) — it can never admit ill-typed Core. If SP3 ever seems to need a kernel/core change, it
is mis-scoped → HALT and update this file.

### THE BIG WIN — the "one new engine" §4.4 calls for MOSTLY ALREADY EXISTS
Spec §4.4 says the single implementation cost is *type-directed* generation ("give me a well-typed term of type
`T`", stronger than "give me some well-typed term"). **That generator already exists and is callable:**
- `Antigen.Generators.Term.gen_term(ctx, goal)` (`lib/antigen/generators/term.ex:28`) → returns an
  `Antigen.Gen.t()` that samples a **well-typed Core term of type `goal`** in context `ctx`. It is mode-directed
  inversion of the kernel's bidirectional rules with a canonical-inhabitant fallback (`SigMenu.canon/2`) so it is
  **total** (never fails to produce *a* term). `@max_size 12`, fuel `@gen_fuel 500`.
- So SP3's real work is **WIRING** `gen_term` into per-hole filling — NOT building type-directed generation from
  scratch. The remaining generator work is only mapping a grammar hole `<n: Category>` → the Core `goal` type to
  pass to `gen_term`, and only for the hole categories a DSL actually uses (spec §4.4: base value/data types
  first; higher-order/dependent hole types a later increment; a hole type outside reach must be REPORTED as a
  coverage gap, per §4.2, not silently passed).

### Reusable machinery inventory (all verified present — do NOT reinvent)
- **Type-directed term gen:** `Antigen.Generators.Term.gen_term(ctx, goal)` (above). Context generation:
  `Antigen.Generators.Context.gen/1`; signature menu `Antigen.Generators.SigMenu` (`env_of/1`, `rebuild_context/2`,
  `canon/2`).
- **Gen monad combinators:** `Antigen.Gen` (`lib/antigen/gen.ex`): `return/1`, `member_of/1`, `one_of/1`,
  `frequency/1`, `bind/2`, `sized/1`. Interpreted by backend `Antigen.Backend.StreamData` (`sample/2`,
  `sample_seeded/3`). Use `bind`/`sized`/`return` to assemble a whole-program generator from per-hole `gen_term`s.
- **Shrinker (for the counterexample):** `Antigen.Shrink.minimize(challenge, pred, budget)`
  (`lib/antigen/shrink.ex:13`); `candidates/1`, `size/1`. It already shrinks `:typed_term` payloads — the
  counterexample a macro reports should be shrunk through this so the author sees the SMALLEST offending input.
- **Challenge record:** `Antigen.Challenge.new(kind:, assay:, label:, payload:, seed:)`. SP3 likely adds a new
  `kind` (e.g. `:macro_expansion`) with payload `%{macro: <name>, rule: <kw>, input: <generated parse>, expansion:
  <Core>, ...}` — or fuzzes OUTSIDE the Challenge/assay registry entirely (a per-macro-compile loop). DECIDE which
  (see Open Questions).
- **Coverage manifest:** `Antigen.CoverManifest` (`lib/antigen/cover_manifest.ex`): `expected/0`, `hit_points/1`,
  `missing/1`, `summary/1`, `report/1`. SP3 needs a **per-macro** manifest (which rules + which `fail`/`explain`
  points were exercised, at what depth). Model it on CoverManifest but keyed by macro definition, per spec §4.2.
- **Runner/campaign:** `Antigen.Runner` (`generate/1`, `replay/2`, `@registered_assays`). Relevant if SP3 registers
  an assay; skippable if SP3 runs its own per-compile loop.

### The expansion path SP3 must call (what "expand `p`" means concretely)
- **Tier-1/2 (template `becomes`, built in SP1):** `Cure.Compiler.Parser.expand_example(rules, use_site_tokens)`
  (`lib/cure/compiler/parser.ex:146`) parses a use-site token stream against a macro's `rules` and returns the
  expansion AST (it wraps a sentinel `{:example_use_site_not_fully_consumed,…}` if the input isn't a single full
  use — reuse that discipline). This is the exact function `MacroValidate.check_examples` uses to expand the
  worked examples; SP3 does the same but with GENERATED inputs instead of author examples. **A generated program
  is a token stream** (or an AST you can render to tokens) — the generator's job is to produce hole-fillers, splice
  them into the rule's use-site shape, and hand tokens to `expand_example`.
- **Tier-3 (`computed by`, SP2 slice 3 — NOT YET BUILT):** its expansion is the compile-time execution pass
  (`elaborate elab → normalise(app(elab, input)) → from_syntax → splice → re-elaborate`, see the SP2 NEXT block
  above and `…-tier3-computed-by-execution-design.md`). **SP3 CANNOT fuzz Tier-3 macros until SP2 slice 3 lands.**
  Program-doc confirms: SP3 "Depends on SP2 (needs Tier-3 elabs + the grammar to fuzz)." → **Sequence: finish SP2
  (incl. slice 3) FIRST.** SP3 CAN be prototyped against Tier-1/2 macros (which fully exist) to build the generator
  wiring + gate + manifest, then extended to Tier-3 once slice 3 exists.
- **Kernel-check the expansion:** re-elaborate the expansion on the dependent pipeline —
  `Cure.Elab.Program.elaborate/1` (returns `{:ok, env}` | `{:error, …}`). SP1 T8 already built the
  "expansion expands to WELL-TYPED Core" dependent firewall (commit `3a7383d`; see the transitional classic one
  in `test/cure/compiler/macro_expansion_classic_soundness_test.exs`). SP3 generalizes that single firewall to
  the fuzzed-input population. A kernel `{:error, …}` on a valid generated parse == the SP3 counterexample.

### The check host & the wiring seam (where the gate fires)
- SP2's self-proving checks live in **`Cure.Compiler.MacroValidate`** (`lib/cure/compiler/macro_validate.ex`):
  `check_explain_exhaustive/1` → `{:error,{:missing_diagnosis,points}}`, `check_rules_pinned/1` →
  `{:error,{:rule_unpinned,names}}`, `check_examples/1` → `{:error,{:example_mismatch,details}}`. **SP3 adds a
  fourth sibling here:** `check_expansion_proof/1 :: (macro_def) -> :ok | {:error,{:expansion_ill_typed, %{input, expansion, kernel_error, shrunk}}}`.
  Error atoms/formatting go in `lib/cure/compiler/errors.ex` alongside the other three.
- **WIRING CAVEAT (shared with SP2):** these `MacroValidate` checks are currently STANDALONE — grep shows only
  comments reference them from the compile pipeline; they are not yet invoked on every real compile. SP2's own
  "WIRING slice" (see SP2 NEXT block) is what threads `MacroValidate` into the compile path. **SP3's full-fuzz
  gate needs that SAME wiring seam.** Coordinate: either SP2's wiring slice lands the seam and SP3 hangs its
  check on it, or SP3's first slice builds the seam. Do NOT assume the checks auto-run — verify with a red test
  that a bad macro actually FAILS TO COMPILE (not just that `check_*` returns an error in isolation).

### Proposed SP3 slice decomposition (each slice = full autopilot Stage 2–6, red-test-first, committed)
Order chosen so each slice has a runnable red test and builds on the last. Adjust if grounding contradicts.
1. **Slice A — hole-type → Core-goal mapping + single-hole generation.** Given one rule with one typed hole
   `<n: Category>`, produce a `Gen` of a well-typed filler via `gen_term(ctx, goal)`. RED TEST: for a hole of a
   base type (e.g. `Int`/`Bool`/a simple ADT), the generator yields N terms that each `elaborate`/infer to that
   type. Report `:unsupported_hole_type` for a category outside reach (coverage gap, not a pass).
2. **Slice B — whole-parse assembly.** Splice per-hole fillers into a rule's use-site shape → a full generated
   use-site token stream; feed `expand_example` → an expansion AST. RED TEST: a generated parse for a known-good
   Tier-2 macro expands without the not-fully-consumed sentinel.
3. **Slice C — the property + gate.** For a batch of generated parses: expand each, `elaborate/1` the expansion,
   collect kernel errors. RED TEST (the headline): a **deliberately broken** macro whose `becomes` drops a hole's
   type (so a valid parse expands to ill-typed Core) is REJECTED at compile with a counterexample; a correct macro
   PASSES. This is the program-doc SP3 gate. Use a hand-written broken fixture macro as the negative control.
4. **Slice D — shrink the counterexample.** Route the failing generated input through `Antigen.Shrink.minimize/3`
   so the reported counterexample is minimal. RED TEST: the reported input for the broken macro is the minimal
   failing shape (assert size ≤ a bound, or equals a known minimal witness).
5. **Slice E — per-macro coverage manifest + caching.** Manifest records rules/`fail`/`explain` points exercised
   and depth; cache keyed by macro definition (same grammar+elabs ⇒ reuse prior PASS; edit ⇒ re-run full).
   RED TESTS: manifest lists all rules of a multi-rule macro; an unchanged macro's second compile does not re-fuzz
   (observable via a call counter/flag), an edited one does. Caching is "don't redo identical work," NEVER a
   weaker gate (spec §4.2).
6. **Slice F — wire the full-budget gate into every macro compile** (or hang on SP2's wiring seam) + extend to
   Tier-3 `computed by` macros once SP2 slice 3 exists. RED TEST: end-to-end, a user macro in a `.cure` source
   with a latent expansion bug fails `Cure.Elab.Program.elaborate/1` of the whole program with the SP3 error.

### SP3 GATE (from program-doc — the acceptance bar)
"A macro whose `becomes`/elab drops a hole's type is REJECTED at macro-compile with a shrunk counterexample; a
correct macro passes; the manifest reports coverage. Full suite green; Antigen campaign green." Plus the
DONE-criterion end-to-end proof: a user macro parses, expands, is generatively proven, and its expansion runs.

### Open questions to DECIDE early (don't guess silently — record the decision in this file)
1. **Assay-registered vs standalone loop?** Register a new `:macro_expansion` assay in `Antigen.Runner`
   (`@registered_assays`) and reuse the campaign/replay/corpus banking, OR run a self-contained per-macro-compile
   fuzz loop that only borrows `gen_term`/`Shrink`/manifest. Standalone is simpler and matches "gates every macro
   compile"; assay-registration buys corpus replay + the existing coverage campaign. Prior lean: **standalone loop
   that borrows the pieces** (macro fuzz is per-compile, not part of the kernel campaign) — but confirm against how
   heavy the full-budget run is and whether corpus banking is wanted. NOTE the standing rule: **revert
   `test/antigen/seeds.sexp` + `corpus.sexp` banking noise before committing** — if SP3 runs anything that banks
   seeds, scrub that diff.
2. **Grammar-hole → Core-type bridge.** How does a rule declare a hole's TYPE, and where is it stored on the
   `{:macro_def, meta, rules}` AST? Probe the harvested rule shape (`harvest_active_macros`, parser.ex:183) and the
   Tier-2 `syntax` rule's hole-kind field before Slice A — the mapping from a hole's declared Category to the Core
   `goal` term is the crux and is under-specified here.
3. **Budget/perf.** "Full budget on every compile" is a deliberate cost (spec §4.2). Pick a default draw count
   (Antigen defaults `count: 200`, `gen_term` size ≤ 12). Caching (Slice E) is the escape valve.

### Two-pipeline steer (put this in EVERY SP3 subagent brief — verbatim)
Dependent machinery lives ONLY in `lib/cure/elab/*` + `lib/cure/core/*`. IGNORE `lib/cure/types/*`
(`checker.ex`, `unify.ex`) and the codegen half of `lib/cure/compiler/*` (`codegen.ex`, `pattern_compiler.ex`) —
non-dependent lowering; same-named functions are decoys. For SP3 the RIGHT anchors are: the generator
`lib/antigen/generators/term.ex` (`gen_term/2`), the expansion entry `lib/cure/compiler/parser.ex`
(`expand_example/2`, `harvest_active_macros`), the check host `lib/cure/compiler/macro_validate.ex`, and the
kernel-check via `Cure.Elab.Program.elaborate/1`. A read-only scouting agent that greps by name will land in the
wrong pipeline and report phantom "type-directed generation missing" — it is NOT missing (`gen_term/2` is it).

### Standing rules recap (same as the rest of this run)
Ghost commits `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. Explicit pathspec
`git add -- <path>`, never `-A`. Revert `test/antigen/seeds.sexp`/`corpus.sexp` banking noise before committing.
ONE `mix` suite at a time (prefer scoped `mix test <file>`; full suite once, alone, at the gate). Commit per
stage/task. Reviews on Sonnet (`model: sonnet`, recursive-skeptical-review to two clean passes), implementation on
Opus. STOP + update this file + PushNotification on a hard blocker or pass-15 non-convergence — never accept an
unconverged artifact. Tests immutable once green.

### Cross-refs
- Spec §4: `docs/superpowers/specs/2026-07-11-self-proving-macros-design.md:174-241`.
- Program-doc SP3: `docs/superpowers/plans/2026-07-12-macro-facility-program.md` ("### SP3").
- Tier-3 execution design (needed before SP3 can fuzz Tier-3): `docs/superpowers/specs/2026-07-12-tier3-computed-by-execution-design.md`.
- SP1 T8 expansion firewall (the single-case ancestor of SP3's fuzz): commit `3a7383d`,
  `test/cure/compiler/macro_expansion_classic_soundness_test.exs`.
- Antigen metatheory engine + coverage discipline: project memory `[[antigen-metatheory-engine]]`,
  `[[antigen-coverage-manifest]]`, `[[antigen-coverage-plateau]]` (~95% honest ceiling — SP3 inherits the same
  "statistical, not a formal proof for an infinite grammar" residual, spec §4.5; state it, don't overclaim).

## DONE criterion (cancel cron + notify)
All 6 sub-projects implemented, code-reviewed, full `mix test` green, with an end-to-end
proof: a user-defined macro parses, expands, is generatively proven to expand to
well-typed Core, and its expansion runs. Then CronDelete + PushNotification.

## HALT protocol
Hard blocker or a review loop hitting pass 15 without convergence → update THIS file with
the blocker + what's needed, PushNotification, STOP. Never guess or accept an unconverged
artifact.

## Live implementation state — 2026-07-12

The following slices have now landed in this worktree:

- SP2 type-only example pins and dependent-pipeline validation wiring are complete.
- SP3 slices A–F are implemented in `Cure.Compiler.MacroFuzz`: typed-hole generation, multi-hole use-site assembly, generated expansion checking, shrinking, proof manifests, persistent cache reuse, and computed-rule coverage are present. Built-in lexical domains use explicit native generators, and closed custom enum categories resolve from real module environments. The built-in `Code` proof domain is deliberately numeric to preserve the existing macro contract; arbitrary expression categories still require a later typed-domain extension.
- SP4 has an advisory reflection foundation in `Cure.Compiler.MacroReflection`: definition/type resolution, constructor inspection, dependent type inference, macro expansion, and pure declaration lifting.
- SP4 also has a reflection-backed reducer dogfood builder in `Cure.Compiler.MacroReducer`; it emits ordinary `pattern_match` AST and proves it through the dependent elaborator.
- SP5 has a closed OTP callback vocabulary, callback ADT-shaped values, declaration validation, and pure `QuotedModule` lifting in `Cure.Compiler.OtpMacro`; it does not load or compile generated code.
- SP6 has delimited raw-hole parsing, pure capture helpers, computed use-site integration, `is Category` rule metadata, and explicit module-rule markers.
- SP6 raw-hole proof fixtures now generate bounded raw text and preserve a synthetic `dedent` delimiter through `MacroFuzz`/`Parser.expand_example`.
- SP3's built-in lexical categories now use native domains: numeric literal generators for `Number`/`Duration`, mixed typed expression generators for `Code`, and type-term generation for `Kind`. Unsupported categories remain explicit coverage errors.

The remaining work before the DONE criterion is genuinely satisfied is:

- Extend native generation from the current closed built-in domains to module-aware/custom category declarations and explicit open-category coverage reporting.
- Verify or complete the generated-proof gate across every real macro compilation path, including the transitional classic compiler path where the architecture requires it.
- Extend SP4 from the base reflection API to the reducer/view/flow dogfood surface and its integration tests.
- Extend SP5 to the complete `behaviour`/`callback`/`lift module` surface, closed callback ADTs, and the AtomVM execution gate.
- Extend SP6 from the current raw integration and metadata to full module-rule execution, open-category composition, repetition/optional grammar groups, and the concrete DSLs specified by the macro design.
- Perform the required skeptical review, full test gate, Antigen verification, and final end-to-end proof before declaring completion.

Do not mark the DONE criterion complete until every item above is implemented and verified.
