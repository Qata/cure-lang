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

**NEXT:** SP1 milestone 2 Stage 5 — dispatch a Sonnet `recursive-skeptical-review` subagent over
the Stage-4 diff (`git diff e6883fe..HEAD` is plan+state; the code diff is `754e8d0..HEAD`, i.e.
commits d66bf57/0bd320f/94c33a6 touching only `lib/cure/compiler/parser.ex` +
`test/cure/compiler/macro_use_test.exs`). Code review = falsifiability in full force, red-test-first
fixes, two consecutive clean passes. Then Stage 6 (full `mix test` once) for milestone 2.
T4/T7/T8/T9 remain subsequent Stage-2/4 rounds before SP1's own Stage 6 + SP2. When ALL SP1 tasks
are executed + code-reviewed, do SP1 Stage 6, update this file, start SP2.

## DONE criterion (cancel cron + notify)
All 6 sub-projects implemented, code-reviewed, full `mix test` green, with an end-to-end
proof: a user-defined macro parses, expands, is generatively proven to expand to
well-typed Core, and its expansion runs. Then CronDelete + PushNotification.

## HALT protocol
Hard blocker or a review loop hitting pass 15 without convergence → update THIS file with
the blocker + what's needed, PushNotification, STOP. Never guess or accept an unconverged
artifact.
