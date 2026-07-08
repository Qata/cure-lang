# Automatic dependency-ordered compilation (DepGraph) — Design

**Date:** 2026-07-08
**Status:** Approved (operator design gate, autopilot run)
**Topic:** auto-import-order

## 1. Problem

Cure's build entry points maintain module ordering by hand or by accident:

- `Mix.Tasks.Cure.CompileStage1.stage1_group/1` is a hand-numbered 0–10 table
  ordering the self-hosted kernel sources (`lib/mix/tasks/cure.compile_stage1.ex:106-118`).
  It is load-bearing: stage1 modules import each other via
  `use Compiler.Kernel.Core.X` and call each other **unqualified**, and codegen
  resolves those calls by probing **loaded** beams
  (`resolve_import`/`module_exports?`, `lib/cure/compiler/codegen.ex:2050-2069`).
  Because non-`Std.*` imports are never validated, a wrong order does not fail —
  it silently emits **local** calls (`codegen.ex:1204-1213`), producing broken
  beams that `:undef` at runtime.
- `mix cure.compile_stdlib` compiles `lib/std/*.cure` alphabetically.
- Multi-file user compiles (`Cure.CLI.cmd_compile`/`cmd_run`,
  `Cure.Project.compile_project`) never load compiled beams between files, so a
  user module that `use`s a sibling module and calls it unqualified is silently
  miscompiled (local-call fallback) **regardless of argument order**.
- `Cure.Stdlib.Preload`'s source-JIT fallback (`compile_missing_from_sources/1`)
  iterates alphabetically; a classic (non-dependent) module with `use Std.X` can
  hard-fail (`missing_stdlib_module`, `codegen.ex:2020-2046`) if X is not yet
  loadable.
- Selective preload (`preload(kind: :collections)`) loads a group without its
  cross-group runtime dependencies (e.g. beams that remote-call `:core`-group
  modules), because groups are a selection filter with no dependency knowledge.

The operator's directive: replace manual ordering with real compiler machinery —
automatic dependency-graph sorting so modules Just Work, like every serious
language.

## 2. Verified ground truth (fresh-VM experiments, 2026-07-08)

These facts bound the design. Each was verified empirically on this checkout,
not inferred from reading code:

1. **Two codegen pipelines.** `Cure.Compiler.compile_file/2` routes a module
   through the dependent pipeline (`Cure.Elab.Program` → Core →
   `Cure.Elab.Emit`) when `Elab.Program.dependent?/1` holds
   (`lib/cure/compiler.ex:259-280`); otherwise through classic codegen
   (`compile_module_container`). The dependent pipeline re-elaborates imported
   **source files** (`import_source_env`, `lib/cure/elab/program.ex:592-630`) and
   never probes beams: `vector.cure` (`use Std.Nat`, `use Std.Bounded`) compiles
   correctly in a fresh VM with `Cure.Std.Nat` unloadable.
2. **Qualified calls are order-free.** `Std.Map.get(...)`-style calls lower
   syntactically to remote calls (`compile_qualified_call`,
   `codegen.ex:1222-1229`) with no load probe. `access.cure` (no `use` lines,
   all cross-module calls qualified) compiled in a fresh VM with
   `Cure.Std.List` unloadable produces a beam whose import table correctly
   references `Cure.Std.List`, `Cure.Std.Map`, `Cure.Std.Pair`.
3. **Implicit no-`use` references are not cross-module edges at compile time.**
   References like `Equivalent`/`reflexive`/`True` in `decision.cure` resolve
   from the builtin-inductive seed (`Cure.Core.Builtins.seed`,
   `program.ex:133`) and the auto-prelude (`Std.Bool`, `Std.Nat`;
   `program.ex:240`), all source-based.
4. **The only load-sensitive machinery** is classic codegen's
   `validate_stdlib_imports/1` (hard error, `Cure.Std.*` only — confirmed live
   with a `use Std.Nonexistent` probe → `{:codegen_error,
   {:missing_stdlib_module, ...}}`) and `resolve_import/3` (silent local-call
   fallback, all imports). Both probe `:code.ensure_loaded` +
   `module_info(:exports)`.
5. **Runtime cross-module call graph** (beam import tables): stdlib —
   Access→{List,Map,Pair}, Functor→List, Gen→List, NonEmpty→List,
   Set→{List,Map}, Signal→{Eq,Ord}, Signal.Event→Eq,
   Signal.Flow.Graph→{Clock,Fsm,List,Signal.Flow,String}; stage1 — the full
   kernel-core mesh (TypeChecker→{Declaration,Environment,Expr,Level,
   LocalContext,Name}, Environment→{...,TypeChecker}, etc.) plus Std.{List,
   String,Test}.
6. **Both current `use` graphs are DAGs.** Note Environment↔TypeChecker call
   each other at **runtime** (beam import tables, fact 5) — mutual recursion is
   fine at runtime — but their `use` declarations are acyclic, which is what
   ordering needs. (Only 2 of 39 stdlib modules declare `use` at all;
   stage1 kernel modules declare `use` comprehensively.)
7. **`__group__` is selection, not ordering.** It drives `preload(kind:)`
   filtering (`lib/cure/stdlib/preload.ex:309-320`); order within a selection is
   `Enum.sort()`. Live consumers of the kind API: `cure run`,
   `mix cure.check.examples`, the test suite, and `Cure.REPL.Config`
   (validates against `known_groups/0`). The sources-absent release fallback
   `discover_from_beams/1` calls the exported `__group__/0` on packaged beams
   (`preload.ex:345-376`).

## 3. Design overview

Build-orchestration machinery only. **No kernel/TCB changes, no elaborator
changes, no new surface syntax, no manifest/package system.** Codegen's
qualified-call and dependent-pipeline paths are already order-free and are left
alone; we make every build entry point feed them files in dependency order and
keep compiled output loadable as the pass proceeds.

### 3.1 `Cure.Compiler.DepGraph` (new, `lib/cure/compiler/dep_graph.ex`)

Pure Elixir module (no process state). Input: a list of `.cure` paths — a
*compile set*.

**Per-file scan** via the headless front-end `Cure.Compiler.parse_source/2`
(commit `eacfdfa`; lex+parse only, no app boot):

- **Declared module name**: from the AST container node, covering all container
  kinds (`mod|proof|actor|fsm|sup|app`) — semantics matching Preload's
  `@mod_regex` but AST-based, not regex.
- **Order-edges**: targets of `use` declarations (`{:import, meta, _}` nodes,
  `meta[:source]`), restricted to modules declared **within the compile set**.
  Out-of-set targets (e.g. `Std.*` from a stage1 file) impose no intra-set
  ordering; their availability is already handled by preload/validate.
- **Closure-edges** (superset, for load/JIT closure — not ordering): `use`
  targets + qualified-call targets (AST walk for dotted callee names, module
  part per `compile_qualified_call` semantics, filtered to the known module
  universe so Erlang externs are never edges) + auto-prelude modules
  (`Std.Bool`, `Std.Nat`, minus the self/declared-type exclusions mirroring
  `auto_prelude_imports/1`).
- A file that fails to parse contributes no edges and is reported
  (`{:error, {:parse, path, reason}}`) — the build task decides whether to
  proceed (existing per-file error handling) — except placeholder (blank)
  sources, which are skipped exactly as `cure.compile_stage1` does today.
- Two in-set files declaring the same module name is an error
  (`{:duplicate_module, name, [path1, path2]}`).

**API** (shapes indicative):

```elixir
@spec scan([Path.t()]) :: {:ok, graph} | {:error, reason}
@spec order(graph) :: {:ok, [Path.t()]} | {:error, {:import_cycle, [module_info]}}
@spec closure(graph_or_baked_map, [module_atom]) :: [module_atom]
```

`order/1`: Kahn/Tarjan topological sort over order-edges with **alphabetical
tie-break** among ready nodes — fully deterministic, so repeated builds compile
in identical order.

**Cycle policy: hard error.** A `use` cycle among in-set modules is rejected
with a new error code, listing the cycle as `A (a.cure:3) -> B (b.cure:2) ->
A`, using the next free `E`-code in the `Cure.Compiler.Errors` registry
(E091 expected; implementation verifies against the registry and takes the
actual next free code). Rationale: OCaml, Haskell, and Rust reject module-level
import cycles; both current Cure graphs are DAGs; runtime mutual recursion
(Environment↔TypeChecker) does not require cyclic `use` since the `use`
declarations themselves are acyclic today. If a genuine need appears, modules
can merge or the policy can be revisited — the error message says so.

### 3.2 Build entry-point integration

1. **`mix cure.compile_stage1`**: delete `stage1_group/1` and
   `stage1_sort_key/1`; order via `DepGraph.order/1`. Keep: placeholder skip,
   `--include-tests` filtering (test files sort naturally after their deps;
   the flag continues to include/exclude them), `Code.prepend_path` before
   compiling (already present — this is what lets the ordered pass resolve
   earlier beams).
2. **`mix cure.compile_stdlib`**: order via DepGraph instead of `Enum.sort()`,
   and move the output-dir code-path registration to **before** the compile
   loop (mirroring stage1). Today this changes nothing observable (fact 2/6) —
   it makes the pass principled and future-proofs classic `use` inside the
   stdlib.
3. **`Cure.CLI.cmd_compile` / `cmd_run` (multi-file) and
   `Cure.Project.compile_project`**: order the file list via DepGraph and
   **load each emitted beam immediately after compiling it** (the
   `Preload.load_if_present/2` pattern — `:code.load_binary`, no global path
   pollution). This makes user→user `use` + unqualified calls link correctly.
   Single-file invocations are unaffected (a one-node graph).
4. **`resolve_import` silent fallback → warning.** When a `use`-imported
   unqualified call resolves to no import and falls back to a local call
   (`codegen.ex:1208-1213`), emit a compiler warning through the existing
   per-file `warnings` channel naming the function and the modules probed.
   Behavior is otherwise unchanged (no new hard error — existing workflows that
   rely on late loading keep working, but silence is removed).

### 3.3 `Cure.Stdlib.Preload` — closure-aware selection

- Extend the existing compile-time scan (same `@external_resource` baking
  pattern) to also bake `%{module => [closure_dep_module]}` using
  `DepGraph`-equivalent extraction. Groups and `@mod_regex`/`@group_regex`
  stay; the new map is additive. (The scan may reuse DepGraph's parser-based
  extraction; if parsing at Elixir compile time is unacceptable there — e.g.
  parser not yet compiled in the same pass — a documented regex fallback for
  `use` + qualified-call heads is acceptable, since stdlib style is enforced
  in-repo. The implementation plan decides with evidence; behavior, not
  mechanism, is normative here.)
- `preload(kind:)` expands the selected module set to its **closure** over the
  baked dep map before loading (e.g. any selection pulling `Std.Signal` also
  loads `Std.Eq`/`Std.Ord`). Selection *semantics* (which groups the user asked
  for) are unchanged; closure only adds modules needed for the selection to
  actually run.
- `compile_missing_from_sources/1` (source-JIT) iterates its module list in
  dependency order (closure map restricted to order-edges is sufficient;
  alphabetical tie-break).
- **Unchanged and explicitly preserved**: `__group__` convention in sources,
  `known_groups/0`, the `kind` API and its validation in `Cure.REPL.Config`,
  and the `discover_from_beams/1` release fallback. In the beams-only fallback
  the dep map is empty → closure degrades to plain selection (status quo).
- `docs/STDLIB.md` gains a paragraph: groups are selection tags; ordering and
  load closure are automatic (DepGraph).

### 3.4 What `__group__` becomes

Nothing changes in sources. `__group__` was never an ordering mechanism
(fact 7); it remains the selection tag for REPL/preload kinds. The *manual
ordering* being retired is the stage1 numeric table plus the alphabetical
accidents; DepGraph replaces those.

## 4. Error handling summary

| Condition | Behavior |
|---|---|
| `use` cycle within a compile set | Hard error, new E-code, cycle path with file:line |
| Duplicate module name in a compile set | Hard error naming both files |
| In-set file fails to parse | Per-file error via existing channel; ordering proceeds for the rest (parse failure will also fail that file's own compile) |
| `use` target not in set and not loadable (classic module) | Existing `missing_stdlib_module` for `Std.*` (unchanged); **new warning** for the silent local fallback on any import |
| Release / sources-absent preload | Closure degrades to selection; groups still work via `__group__/0` beam export |

## 5. Testing

TDD throughout; every behavioral claim below is a red test before its
implementation lands.

1. **DepGraph unit tests** (`test/cure/compiler/dep_graph_test.exs`): ordering
   respects order-edges; deterministic output (same input → same order, ready
   set tie-broken alphabetically); cycle → `{:error, {:import_cycle, ...}}`
   with the full path; duplicate module error; out-of-set `use` ignored for
   ordering; closure includes qualified-call targets (fixture mirroring
   Access→List/Map/Pair) and auto-prelude edges with the self-exclusions.
2. **Stage1 parity** (red first): property test on the real `lib/compiler`
   tree — for every in-set `use` edge A→B, `index(B) < index(A)` in
   `DepGraph.order`; the hardcoded table is deleted only after this passes, and
   `mix cure.compile_stage1` output stays `0 errors` with identical module set.
3. **User multi-file linkage** (red first — fails today): two-file fixture
   where `b.cure` `use`s `A` and calls it unqualified; compile via the
   Project/CLI path into a fresh output dir; assert `b`'s beam import table
   contains the remote call to `Cure.A`. Also assert the adversarial file
   order (B listed first) produces the same result.
4. **Fallback warning**: a classic module whose imported call resolves nowhere
   emits the new warning (and still compiles).
5. **Preload closure**: with a controlled fixture (or the baked map directly),
   selecting a group whose member has a cross-group closure dep loads the dep;
   beams-only fallback degrades to selection.
6. **Full `mix test` suite green**; `mix cure.check.examples` and the stage1 +
   stdlib build tasks run clean. One build/test run at a time (hard
   constraint).

## 6. Out of scope

- Kernel/TCB, elaborator, unification, or any dependent-types semantics.
- New surface syntax (no `import` keyword changes, no manifests).
- Rewriting classic codegen's resolution (qualified + dependent paths already
  order-free); the loaded-beam probe stays, now fed by ordered+loaded builds.
- AtomVM/esp32-beam scripts (they benefit transitively via the CLI).
- Renaming `__group__` or restructuring stdlib groups.
- The `Registry`-based protocol cross-module dispatch (`resolve_protocol_call`)
  — separate concern, unchanged.

## 7. Constraints for implementation

- Compile Cure with OTP 26–28 (AtomVM constraint, repo-wide).
- Never run two full build/test passes concurrently.
- `Cure.Compiler.parse_source/2` is the only front-end entry DepGraph may use
  (headless; degrades gracefully without the started app).
- Preload's compile-time baking must keep the `@external_resource`
  invalidation property for every scanned source.
- Deterministic ordering is a hard requirement (reproducible builds).
