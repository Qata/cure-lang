# Refinement-types removal (task #19) — Design

## §0 Decision record

Operator order (2026-07-09, post-parity teardown batch): remove refinement types ENTIRELY for now; they return only when SMTCoq-style proof reconstruction is ported (task #20, sequenced after everything else). This supersedes the operational "Z3 refinement checking always present" stance for the SOLVER layer only — the **z3 binary dependency itself stays**, because GuardLint (the dependent pipeline's guard-coverage lint) is NOT refinement machinery and keeps using `Cure.SMT.Process`. The SMT trust-boundary decision (Z3 out of the TCB) is unchanged and is exactly what makes this removal kernel-silent.

**Scout-verified foundation:** refinement types are a CLASSIC-pipeline-only feature. The dependent pipeline already treats them as nonexistent — `program.ex:403-406` drops `refinement: true` type_annotations, `declarations.ex:233` never matches the 3-element refinement alias parts, `program.ex:233` excludes `Std.Refine` from the dependent auto-prelude. **Zero changes to `lib/cure/core/*` or `lib/cure/elab/*`** (one doctor.ex string aside) — the TCB is untouched by construction.

**Coordination with task #18 (classic-pathway work):** #19 OWNS all refinement machinery wherever it lives, including the classic-side files; #18 (whatever its final scope) must not double-delete. Sequencing: #17 (lean bridge) → #19 (this) → #18.

## §1 Cut line — DELETE

**Parser grammar (the shared front end — the one non-classic code change):**
- `parser.ex:3372-3387` `parse_refinement_type/1`; `parser.ex:3036-3041` (`type Name = {x:T|p}` alias form); `parser.ex:4349-4353` (inline `{x:T|p}` in type positions). `{x: T | p}` becomes an ordinary parse error — no bespoke "removed feature" diagnostic kept in the grammar (the removal is recorded here and in the changelog line of the commit; less dead code beats a nicer message for a feature returning via a different mechanism later).

**SMT refinement-query layer (`lib/cure/smt/` split, not delete):**
- DELETE `solver.ex`, `translator.ex`, `parser.ex` (refinement-only: subtype/sat/implication queries over surface-AST predicates; parser.ex's sole consumer is solver.ex:150).
- KEEP `process.ex` IN PLACE (GuardLint's Z3 port GenServer; relocation would churn GuardLint for zero benefit).

**Classic-pipeline refinement machinery (all under `lib/cure/types/`):**
- DELETE `refinement.ex`, `guard_refinement.ex`, `path_refinement.ex`, `pattern_refinement.ex`, `dependent.ex` (classic dependent-lite VCs, SMT-discharged — refinement family).
- STRIP every `{:refinement,…}` clause / refinement field from: `checker.ex` (24 hits incl. `discharge_refinement`/`verify_return_refinement` ~2725-2750 and the check_sat call at 2181), `type.ex` (subtype/join/compatible clauses), `unify.ex` (strip clauses :103-108/:237/:261-262), `env.ex` (`refinement_assumptions`/`refinement_var_types` fields), `stdlib.ex` (Std.Refine name-mapping rows :36/:110/:180/:345-346), `pattern_checker.ex`, `reduce.ex`. (`core_bridge.ex:20` is a comment — update the prose.)

**Peripheral `{:refinement,…}`/SMT consumers:**
- `export_types/protobuf.ex:209-211` (E068 clause), `optimizer/monomorphise.ex:196/449`, `doc/extractor.ex:167/186` + `doc/html_generator.ex:500-501`, `compiler/errors.ex` E090/W091 formatters (:56-73) + E015/E018/proof-container refinement prose, `compiler/printer.ex` refinement rendering, `project/proof.ex` + `proof/verifier.ex` `:refinement`/`:smt` manifest kinds (offline Z3 replay stub), `pgo.ex`/`pgo/profile.ex` SMT-latency hooks, `bless.ex:5`/`bless/advisor.ex:15` mentions, `mix.exs:122` + `lib/cure.ex:4` "SMT-backed verification" strings.

**Stdlib + examples:**
- DELETE `lib/std/refine.cure` (group-tag discovered; no Preload entry to edit).
- DELETE pure-refinement examples: `examples/refine_predicates.cure`, `examples/path_refinement.cure`, `examples/byte_size_refinement.cure` + their `cure.check.examples` expectation rows (`mix/tasks/cure.check.examples.ex:49/:55`) + README mentions.
- REWRITE mixed examples (they merely use aliases): `examples/dependent_types.cure` (3 aliases), `examples/cure_motif/cure_src/motif.cure` (Pitch/Velocity/Channel/Bpm…), `examples/cure_moneta/cure_src/moneta.cure` — each `type X = {v: B | p}` becomes `type X = B` with a one-line comment noting the invariant is unchecked pending SMTCoq. Their check.examples expectations must stay byte-identical (the aliases were classic-erased anyway) — if any expectation changes, STOP (it means the alias was load-bearing beyond typing).

**Antigen refinement/SMT surface:**
- DELETE `assays/smt_lint.ex`, `generators/smt_query.ex`, runner rows `smt/implication|unsat|witness` (`runner.ex:366-368`), the `{:refinement, :int, "x", :positive}` row in `generators/unify_problem.ex:71` + strip clause `assays/unifier.ex:131`, the two refinement surface nodes in `generators/surface_expr.ex:109-110`.

**Tests (deleted WITH their subsystem — enumerated, not weakened):**
- Whole files: `test/cure/smt/smt_test.exs`, `test/cure/smt/solver_k13_test.exs`, `test/cure/types/guard_refinement_test.exs`, `test/cure/types/path_refinement_test.exs`, `test/cure/types/pattern_refinement_narrowing_test.exs`, `test/cure/types/byte_size_refinement_test.exs`, `test/antigen/assays/smt_lint_test.exs`.
- Selective removals (refinement cases inside shared classic test files): `test/cure/types/checker_test.exs`, `stdlib_test.exs`, `unify_test.exs`, `dependent_test.exs`, plus `compiler/errors` refinement prose rows — the plan enumerates each removed test BY NAME with the justification "tests the deleted refinement subsystem"; no surviving test may change.

## §2 KEEP — explicitly, each verified

- `lib/cure/elab/guard_lint.ex` **byte-for-byte** + `lib/cure/smt/process.ex` + `test/cure/elab/guard_lint_test.exs` + `lib/antigen/generators/elab_guard_lint.ex` + runner row `elab/guard_lint` (:350). GuardLint's verdicts gate guard-chain catch-all acceptance (elaborator.ex:2524, kernel re-checks) and shadowing warnings — ordinary pattern guards, not refinements.
- `doctor.ex:103-124` DOC-ENV-Z3 probe and `john.ex:329/:353` z3 path report stay; REWORD doctor's ":115 refinement checks will be skipped" message to reference the guard lint instead.
- ALL Class-C "refinement" hits — kernel `refine_branch`/index-goal refinement in `core/kernel.ex`/`certificate.ex`/`elaborator.ex`/`declarations.ex` and Antigen `challenge.ex`/`indexed.ex`/`branch_unify.ex`/`dep_match.ex` (incl. the `:refine` challenge kind) — are DEPENDENT-MATCH refinement, a different concept, untouched. Any diff touching these files' refinement machinery is a defect.
- Historical specs/docs (incl. `2026-07-03-antigen-smt-lint-design.md`) stay as records; `2026-07-08-guard-coverage-lint-design.md` remains live documentation.
- z3 binary discovery (`System.find_executable("z3")`) in process.ex/doctor/john/… stays.

## §3 Verification gate

1. Full suite green ONCE at the end; delta vs current baseline = exactly the enumerated deleted tests (plan carries per-file counts); zero surviving-test changes (`ctor_guard`/`guard_lint` byte-identical).
2. Antigen green with exactly 3 fewer runner rows; `elab/guard_lint` row still green.
3. Oracle replay 65/65 (plan Step 0 verifies NO oracle fixture uses refinement syntax — if one does, STOP for adjudication); no `mix cure.oracle`.
4. Greps: zero `{:refinement,` under lib/ and test/ (Class-C names like `refine_branch`/`refinement/1` in Antigen indexed.ex excepted by exact-name list); zero `Cure.SMT.Solver|Translator` references; `Cure.SMT.Process` referenced ONLY by guard_lint.ex and its own tests/doctor/john; `parse_refinement_type` gone; `Std.Refine` appears nowhere under lib/ examples/ except historical docs.
5. `lib/cure/core/` diff EMPTY; `lib/cure/elab/` diff EMPTY except the doctor string is not in elab — so elab diff empty full stop. Ghost commits, explicit pathspec, one mix at a time.
6. STOP conditions: any kernel/elab file needs a change; any mixed-example check.examples expectation changes; any surviving test needs modification; an oracle fixture turns out to use refinement syntax; GuardLint behavior changes in any way.

## §4 Non-goals

- Removing the z3 binary dependency or `Cure.SMT.Process` (GuardLint keeps them).
- Touching GuardLint, the kernel, or dependent-match index refinement.
- Deleting `lib/cure/types/` files beyond the five refinement modules (the rest belongs to #18).
- A "feature removed" parser diagnostic (plain parse error; SMTCoq's return will re-add grammar deliberately).
- Editing historical specs.

## §5 Acceptance criteria

1. Refinement syntax is a parse error; `Std.Refine`, the SMT query layer (Solver/Translator/Parser), all five classic refinement modules, every `{:refinement,…}` clause, the Antigen smt surface, and the enumerated tests/examples are gone.
2. GuardLint + Process + their test/assay surface byte-identical; doctor message reworded; z3 stays discoverable.
3. §3 greps clean; core/ and elab/ diffs empty; full suite + Antigen + replay green with enumerated deltas; ghost authorship throughout.
