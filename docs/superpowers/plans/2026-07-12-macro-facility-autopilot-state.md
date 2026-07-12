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

**NEXT:** SP1 milestone 2 — write the Stage-2 plan for tasks T4-T9, then run it through
Stages 3-5:
- T4 `literal` rules + numeric-suffix lexer (`500ms`) — the one lexer change SP1 needs.
- T5 two-phase parse: parser-state `active_macros` seeded by a pre-pass from `use` + local
  `macro` defs (architectural core, grounding doc).
- T6 use-site matching: at a keyword in `active_macros`, walk the rule `segments`, bind
  holes, RECORD progress; port syntax-parse maximal-by-progress when rules compete.
- T7 hygienic `becomes` expansion (`<fresh Name>` gensym) → surface AST.
- T8 feed expansion back through parse→elaborate; assert it kernel-checks (green + a red
  ill-typed-expansion fixture → rejected-not-unsound).
- T9 import scoping + same-keyword conflict; two-pass name resolution.
Plan file: `docs/superpowers/plans/2026-07-12-macro-facility-sp1b-plan.md`. Ground it in
the SP1 grounding doc + the parser anchors already verified. When ALL SP1 tasks (1-9) are
executed + code-reviewed, do Stage 6 (full `mix test` once) for SP1, update this file, start SP2.

## DONE criterion (cancel cron + notify)
All 6 sub-projects implemented, code-reviewed, full `mix test` green, with an end-to-end
proof: a user-defined macro parses, expands, is generatively proven to expand to
well-typed Core, and its expansion runs. Then CronDelete + PushNotification.

## HALT protocol
Hard blocker or a review loop hitting pass 15 without convergence → update THIS file with
the blocker + what's needed, PushNotification, STOP. Never guess or accept an unconverged
artifact.
