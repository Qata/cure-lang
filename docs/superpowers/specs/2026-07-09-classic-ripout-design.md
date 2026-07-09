# Classic-Pathway Full Rip-Out — Design

**Date:** 2026-07-09. **Operator order:** delete the ENTIRE classic (non-dependent) compiler pathway AND every feature that exists only through it — fsm/actor/supervisor/app containers, runtime proto/impl typeclass protocols — with NO porting. Rationale (operator): this is a ground-up rewrite founded on the kernel; while unsound legacy implementations exist, a wayward agent may wire a new kernel-founded feature to them ("oh wait that already exists"). Features die now; they get rebuilt kernel-founded later if wanted.

**Supersedes:** the earlier A-cut/B-port fork analysis. #21 typeclasses is NOT a prerequisite (nothing is ported).

## 0. Non-negotiables

- The dependent pipeline (`lib/cure/elab/*`, `lib/cure/core/*`) becomes the ONLY compiler. `lib/cure/core/` diff must be EMPTY. `lib/cure/elab/` changes are enumerated in §2.3 only.
- The parser/lexer front end STAYS: `lib/cure/compiler/{lexer,parser,parser/precedence,token,beam_writer}.ex` are load-bearing for the dependent pipeline (verified: `elab/program.ex:10` aliases Lexer/Parser, `elab/emit.ex:23` aliases BeamWriter, `elab/declarations.ex:1015` calls `Parser.dotted_path_of`).
- Verified no-cascade: `lib/cure/elab/` + `lib/cure/core/` contain ZERO `Cure.Types.` references (grep, 2026-07-09). Deleting all of `types/*` cannot touch the dependent pipeline.
- Ghost commits, explicit pathspecs, ONE mix command at a time, tests immutable except the enumerated deletions below (each justified as "tests the deleted subsystem"). Any surviving test needing a change = STOP.
- Baseline: record the full-suite numbers at executor start (Step 0) — the nf-idempotence fix may land between spec and execution; do NOT assume 3141.

## 1. Decision records (locked here, operator can veto at merge)

1. **Session-typed `protocol` container (`lib/cure/protocol/*`, v0.27) — DELETE.** Distinct from typeclass proto/impl, but it is a classic-only surface feature with no dependent path; keeping it preserves exactly the "wayward agent" hazard the operator named. Its 10 tests die with it.
2. **`bless.ex` + `bless/advisor.ex` — DELETE.** Both are built around `Cure.Types.Checker.check_module/2` output (bless.ex:72, advisor.ex:18). No classic checker, no bless. CLI wiring for `cure bless` is removed; the subcommand reports removed-in-this-version guidance only if a trivial stub is cheaper than unwiring (executor's call, either is acceptable; no classic code may survive for it).
3. **E043 (raw spawn/receive curated error) — dies with the classic checker.** Post-cut these forms fall through to the dependent elaborator's generic `{:error, {:unsupported_expression, …}}`. The old E043 advice ("use fsm/actor instead") is obsolete anyway — fsm/actor no longer exist. A curated replacement message is a FOLLOW-UP, not in scope. `compiler/errors.ex` keeps front-end (lexer/parser/dep_graph) formatting; classic-diagnostic entries (incl. E043 catalog rows at errors.ex:48, 1117-1118) are removed.
4. **Stdlib rule: a `lib/std/*.cure` module that cannot compile through the dependent pipeline is DELETED**, with per-file reason recorded in the execution ledger. No zombie files, no "held" markers — git history is the archive, modules return when the surface catches up. Known-dead by construction: `fsm/actor/supervisor/app/process` (extern into deleted runtimes) and `access/equatable/functor/ord/show` (proto/impl containers). All other std modules get an explicit Step-0 disposition check (see §4).
5. **Examples rule: an example `.cure` (or example subproject) whose program requires deleted features is deleted**; mixed subprojects lose only their dead files IF the remaining project still builds and its `mix test` passes — otherwise the subproject goes entirely (ledgered).
6. **`observe/top.ex` and `temporal/checker.ex` — DELETE** (built on the deleted FSM/Actor/Sup runtimes; temporal consumes `Cure.FSM.Verifier.extract_transitions`).
7. **Optimizer — DELETE** (`lib/cure/optimizer.ex` + `lib/cure/optimizer/*`): operates on classic forms, `monomorphise.ex` aliases `Cure.Types.{Type,Unify}`, gated off by default.
8. **Downstream consequence accepted by operator:** esp32-beam phase-3 fsm hardware demos break when this merges; out of this repo's scope.

## 2. The cut line

### 2.1 DELETE (whole files/subtrees)

- `lib/cure/types/*` — all 24 files (classic type system incl. core_bridge, reduce, derive, protocol.ex, protocol_registry.ex, synth, holes, effects, …). core_bridge/reduce are kernel CONSUMERS only; nothing in elab/core consumes them back.
- `lib/cure/fsm/*`, `lib/cure/actor/*`, `lib/cure/sup/*`, `lib/cure/app/*`, `lib/cure/process/builtins.ex`.
- `lib/cure/compiler/codegen.ex`, `lib/cure/compiler/pattern_compiler.ex` (parser.ex's only reference is a comment at parser.ex:422 — reword it), `lib/cure/optimizer.ex` + `lib/cure/optimizer/*`.
- `lib/cure/protocol/*` (decision 1), `lib/cure/bless.ex` + `lib/cure/bless/*` (decision 2), `lib/cure/observe/top.ex`, `lib/cure/temporal/*` (decision 6).
- `lib/mix/tasks/cure.synth.ex` (Types-based).
- Antigen classic-layer files (they property-test deleted code): `lib/antigen/assays/unifier.ex`, `lib/antigen/assays/normalizer.ex`, `lib/antigen/generators/surface_expr.ex`, `lib/antigen/generators/unify_problem.ex` + their runner rows + their `test/antigen/*` counterparts. The KERNEL normalizer/conversion assays (Cure.Core-facing) are untouched — the deleted `assays/normalizer.ex` targets `Cure.Types.{Reduce,CoreBridge}` (verify the alias line before deleting; if a file targets Cure.Core, it is the WRONG file — STOP).
- `lib/std/`: `fsm.cure`, `actor.cure`, `supervisor.cure`, `app.cure`, `process.cure`, `access.cure`, `equatable.cure`, `functor.cure`, `ord.cure`, `show.cure`, plus any module failing the §4 disposition check (ledgered).
- Their runtime backings under `lib/cure/stdlib/cure_std_*.ex` ONLY where the std module dies AND nothing surviving references the backing (enumerate in ledger).

### 2.2 CUT-DOWN (mixed files; classic branches excised)

| File | Excise | Anchors |
|---|---|---|
| `lib/cure/compiler.ex` | the `dependent?` fork + classic branch + `maybe_check` + `maybe_optimize` + container-marker `case forms` blocks; result = straight-line Lexer→Parser→`Elab.Program.check_ast_with_locals`→`Elab.Emit.compile_forms`→BeamWriter | 105, 115-130, 217, 223-238, 258-279, 283, 289-301, 351-358 |
| `lib/cure/compiler/errors.ex` | classic-codegen diagnostics + E043 rows; keep lexer/parser/dep_graph/front-end formatting | 48, 1117-1118 |
| `lib/cure/application.ex` | supervision children `Cure.Types.ProtocolRegistry`, `Cure.FSM.Runtime`, `Cure.Actor.Runtime` — SAME COMMIT as the deletions or boot crashes | 9-14 |
| `lib/cure/cli.ex` | `cure check` → route through `Elab.Program.check_ast`; remove bless wiring; `compile_file`/`compile_and_load` calls stay | 750-757 |
| `lib/cure/watch.ex` | `Types.Checker.check_module` → `Elab.Program.check_ast` | 146 |
| `lib/cure/repl.ex` + `repl/session.ex` | classic `Checker.infer_expr`/`register_fn_signature`/`Codegen` paths; REPL keeps compile-and-load evaluation (now single-pipeline). Degraded REPL type-inference is ACCEPTED | session.ex:341-347 |
| `lib/cure/mcp/server.ex` | `check` tool → `Elab.Program.check_ast`; drop the FSM-verify tool | 207, 222 |
| `lib/cure/john.ex` | ProtocolRegistry ETS probe row | 184 |
| `lib/cure/project.ex` + `lib/cure/release.ex` | app-container build path (`Cure.App.Verifier`/`Resource`, `:"Cure.App.<Name>"`), runtime-reference assumptions | project.ex:372,515,702,708; release.ex:189-191 |
| `lib/mix/tasks/cure.{compile,check,check.examples,check.stdlib,compile_stdlib,bundle_stdlib_beams}.ex` | rewire through the single pipeline | per-file |
| `lib/cure/doc/extractor.ex`, `lib/cure/stdlib/cure_std_json.ex`, `lib/cure.ex`, `lib/cure/stdlib/paths.ex` | `Cure.Types.*` references / stale moduledoc diagrams / docstrings | — |

### 2.3 The ONLY permitted `lib/cure/elab/` changes

1. `program.ex`: DELETE `dependent?/1` + `dependent_params?` helpers (the fork is gone; executor greps all callers first — checker.ex and compiler.ex die/are rewired; any OTHER caller = STOP and report).
2. `program.ex`: the §215-233 auto-prelude exclusion comment may need rewording where it names deleted modules (comment-only hunks).
3. NOTHING else. `declarations.ex:155-156`'s `:unsupported_container` catch-all already rejects fsm/actor/sup/app/proto/impl containers — no new code needed.

### 2.4 KEEP (explicit, to protect against over-deletion)

`lib/cure/elab/*` (all), `lib/cure/core/*` (all), `lib/cure/compiler/{lexer,parser,parser/precedence,token,beam_writer,dep_graph,algebra,algebra_formatter,formatter,printer,errors†}.ex` (†cut-down), `lib/cure/pipeline/events.ex`, `lib/cure/stdlib/{preload,paths}.ex` (†paths docstring), `lib/cure/{oracle,cover,doctor,fix,story}.ex`, `lib/cure/smt/process.ex` + `elab/guard_lint.ex` (byte-identical), all kernel/elaborator Antigen files, `test/oracle/**` + replay.

## 3. Entry-point rewire

`compiler.ex:codegen/5` becomes unconditional: `Elab.Program.check_ast_with_locals(ast)` + `Elab.Emit.compile_forms(...)`. Surface forms now failing, with today's vs tomorrow's behavior:

- `fsm/actor/sup/app/proto/impl` containers: parser still produces `{:container, [container_type: …], …}` (parser keyword surface UNCHANGED in this batch — grammar removal is follow-up work); dependent `declarations.ex:103-157` rejects with `{:unsupported_container, …}`.
- raw `spawn`/`receive`, `pickup`, other legacy expressions: elaborator generic `{:error, {:unsupported_expression, …}}` (decision 3).
- `@extern` into deleted runtime modules: compiles only if the module dependent-elaborates; the std modules that do this are deleted (§2.1), so no live path remains.

## 4. Stdlib disposition check (executor Step 0, after baseline)

For each surviving-candidate `lib/std/*.cure` NOT in the known-dead list: attempt `Cure.Elab.Program.elaborate/1` (or the equivalent check entry) via ONE scoped mix invocation (a scratchpad script batching all modules is fine — still one mix command). Ledger each as: DEPENDENT-CLEAN (keep) or FAILS(<reason>) → DELETE per decision 4, including its tests and runtime backing per §2.1 rules. The `program.ex:218-233` exclusion comment predicts `Std.Core` (pickup) and `Std.Equivalent` (:cure_refl) fail — the checker verifies rather than trusts this. Candidates needing individual verdicts: core, gen, crdt, json, http, regex, time, system, io, test, string, list, map, math, nat, iter, set, pair, result, match, decision, bool, sigma, vector, bounded, equivalent, nonempty, proof, and any other present file.

## 5. Test accounting (counts approximate — executor produces the exact ledger)

- DELETE whole dirs: `test/cure/types/` (~262 tests), `test/cure/fsm/` (~58), `test/cure/actor/` (~7), `test/cure/sup/` (~12), `test/cure/app/` (~12), `test/cure/protocol/` (~10), `test/cure/temporal/`, `test/cure/observe/` (runtime-facing files only).
- `test/cure/compiler/`: DELETE classic set — `codegen_test` (~62), `pattern_compiler_test` (~22), `match_spec_test` (~12), `integration_test` (~13), `pickup_test` (~15), `errors_test` (~16, E043) — KEEP the parser/lexer/formatter/dep_graph/front-end set; RE-VERIFY then keep the `dependent_*_codegen_test` set (they exercise `Compiler.compile`'s dependent path, which survives as the only path).
- `test/cure/types/dependent_checker_integration_test.exs`: inspect before deleting — if it tests the dependent fork THROUGH the classic checker entry, it dies with the entry (its coverage exists in `test/cure/elab/`); if it directly exercises `Elab.Program`, relocate is NOT permitted (tests immutable) — report it in the ledger and delete only with that justification recorded.
- Antigen: the 4 classic-layer assay/generator test files + runner-row count drop.
- Audit dirs (`e2e/`, `stdlib/`, `lsp/`, `mcp/`, `cli/`, `doc/`, `test/mix/tasks/`): apply the removal rule — a test dies ONLY if it compiles/needs a deleted feature; each death enumerated with reason. Any test that merely uses `Compiler.compile` on dependent-clean source must survive unchanged.
- Deletion-rule extension (from #19 precedent): non-enumerated tests discovered mid-run that reference the deleted subsystem are deleted as EXTENSIONS, transparently ledgered. A surviving test needing an EDIT = STOP (sole exception precedent: coverage-preserving assertion-list edits à la preload_test in #19, permitted only when the test's subject survives and only the dead-module mention is dropped — each such edit ledgered).

## 6. Verification gates

1. Grep gates (zero hits in `lib/` + `test/` unless stated): `Cure.Types.`, `Cure.FSM`, `Cure.Actor`, `Cure.Sup.`, `Cure.App.`, `Cure.Compiler.Codegen`, `PatternCompiler` (parser.ex comment reworded), `Cure.Optimizer`, `ProtocolRegistry`. Historical docs/site posts are EXCLUDED (dated release notes stay; present-tense claims updated — same rule as #19).
2. `git diff <start>..HEAD -- lib/cure/core/` → EMPTY. `lib/cure/elab/` diff = exactly the §2.3 items.
3. Full suite ONCE at the end: 0 failures; arithmetic reconciled against the Step-0 baseline (baseline − whole-file counts − enumerated selective − ledgered extensions = final). Antigen row-count drop stated; oracle replay 65/65.
4. `mix cure.check.stdlib` (rewired) green over the surviving stdlib; surviving example subprojects' own `mix test` green (each a separate serial mix run).
5. Boot check: the application supervision tree starts (any surviving test run proves this — a boot crash fails everything).

## 7. STOP conditions

- Any surviving test needs a non-ledgered edit; any `lib/cure/core/` diff; any elab/ change beyond §2.3; a `dependent?/1` caller outside compiler.ex/checker.ex; an Antigen file slated for deletion that actually targets `Cure.Core`; a std module failing dependent elaboration whose deletion would orphan a SURVIVING feature (report, don't improvise); needing to keep any part of `types/*` alive for tooling (the tooling gets cut down instead — if that seems impossible, STOP).

## 8. Explicitly out of scope (follow-ups, not silently included)

Parser grammar removal for the dead keywords (fsm/actor/sup/app/proto/impl still parse, then fail elaboration); curated replacement error for spawn/receive; REPL type-inference on the dependent pipeline; #21 typeclasses (separate initiative, brings back Equatable/Ord/Show as interfaces); site/docs deep rewrite beyond present-tense claim fixes.
