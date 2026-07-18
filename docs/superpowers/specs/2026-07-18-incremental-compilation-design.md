# Incremental Cure Compilation

**Status:** design approved, pending implementation
**Date:** 2026-07-18
**Scope:** a general compiler feature (stdlib builds, project builds, and the
test harness that drives them), not a test-only optimization.

## Problem

Every multi-file Cure compile recompiles all modules unconditionally.
`mix cure.compile_stdlib` rebuilds all 81 stdlib modules (~7.5s including the
escript step) on every invocation regardless of what changed, and
`mix cure.compile <dir>` (project builds) does the same over a project's
sources. Because `test/test_helper.exs` runs the stdlib task at the start of
every `mix test`, this fixed cost is also paid on every single-file test run.

The previous "optimization" was a presence check on a sentinel beam. It was
removed because presence cannot notice that a *source changed* since its beam
was built, so it produced ordering-dependent test flakes from stale beams
(`test_helper.exs:17`). Correctness — never serving a stale beam — is the
non-negotiable constraint; speed must not reintroduce that hole.

## Goal

Recompile a module only when its output could actually differ from what is on
disk. Concretely, recompile module `M` iff:

1. `M`'s **source content** changed, or
2. any of `M`'s **output beams is missing**, or
3. any **direct dependency's interface** changed in this build, or
4. the **compiler itself** changed (invalidates everything).

This is interface-level (Swift-style) invalidation: a change confined to a
module's private internals recompiles that module alone; only a change to what
consumers actually elaborate against cascades to dependents.

## Why interface-level is both cheap and sound here

The elaborator already produces, per module, the exact artifact consumers
compile against. `Cure.Elab.Program.compute_module_interface/2`
(`program.ex:1500`) returns a map that already contains a `source_hash` and an
`export_env` — the elaborated environment a consumer merges in when it imports
the module (`load_dependency_env` → `merge_env`, `program.ex:1508-1511`).

Two facts make `export_env` the *complete* channel by which a dependency
affects a consumer's compilation:

- **Cross-module inlining travels inside it.** Inline hints are registered into
  the env via `Env.register_inline_hint` (`mark_inline_hints/2`,
  `program.ex:1740`), so they are part of `export_env`, not a side channel.
- **Codegen does not read dependency beams.** There is no `:code.get_object_code`,
  `:beam_lib`, or `.beam` reading anywhere in the compiler; codegen works from
  the elaborated environment.

Therefore hashing `export_env` is sound **by construction**: if two versions of
a dependency produce a byte-identical `export_env`, every consumer's compilation
input is provably identical, whatever the consumer used from it.

This sidesteps the trap that makes signature-based interface hashing *unsound*
in a dependently-typed language: a consumer's *types* can depend on a
dependency's *value/body* (e.g. `Vec(n)` where `n` is an exported definition),
so a signature hash would miss body changes that matter. An env hash cannot miss
them — the reduced/elaborated value is in the env.

### What is explicitly out of scope: per-consumed-symbol invalidation

Recompiling a consumer only when the *specific* symbols it uses from a
dependency change would require the elaborator to record a per-module *use-set*
(which env entries each module actually touched) and persist it. In a dependent
setting a single type-level reduction can transitively touch many definitions,
so a *complete* use-set is hard to capture without risking a missed dependency
(a stale beam). That is a separate elaborator-instrumentation project. This
design does not attempt it; the interface hash is per-module, not per-symbol.

## Design

### Fingerprints

- **`source_hash`** = `:crypto.hash(:sha256, source_bytes)`. Content-based, so it
  is stable across `git checkout`, `touch`, and mtime granularity, and changes
  only on a real edit. Already computed in `compute_module_interface`.

- **`interface_hash`** = `:crypto.hash(:sha256, :erlang.term_to_binary(export_env,
  [:deterministic]))`. The `:deterministic` flag gives a canonical encoding with
  stable map-key ordering. Computed only for modules actually (re)compiled this
  build; skipped modules reuse their stored hash.

  The `export_env` is obtained from the loader's interface computation, exposed
  as a new public `Cure.Elab.Program.module_interface/2`. This is **not** a
  second elaboration pass on the common paths: the loader already computes and
  caches each stdlib module's interface in `:persistent_term`
  (`cached_module_interface/2`, key `{Cure.Elab.Program, :module_interface,
  path}`) as a side effect of compiling that module's dependents. Computing
  `interface_hash(M)` immediately after M is recompiled primes exactly that
  cache, which M's dependents' compiles then hit — so the interface is elaborated
  once, not twice. The only genuinely extra elaboration is for a changed module
  whose dependents turn out *not* to need recompiling (interface unchanged);
  that is bounded by the number of changed modules and is the very case where
  incremental avoids a full dependent recompile, so it is a net win. Non-stdlib
  (project) sources are not `:persistent_term`-cached (they can change between
  runs), so a project build may elaborate a changed module's interface twice;
  project builds are smaller and less frequent, so this is accepted.

  **Serializability caveat.** `:erlang.term_to_binary` requires `export_env` to
  be a pure data term (no live closures/pids/refs). Cure Core terms are
  tuples/atoms/maps, so this is expected to hold, but the first implementation
  task must verify it on a real stdlib `export_env`. If it does not hold, the
  fallback is to hash a structural projection of the env (its def/family/ctor
  tables) rather than the whole struct — same soundness argument, narrower term.

- **`toolchain`** = a content hash of the compiler's own compiled bytecode — the
  `.beam` files of the `:cure` application in `Mix.Project.compile_path()`,
  concatenated in sorted path order and SHA-256'd. Computed once per build and
  memoized. Any real change to compiler behavior changes this hash; a no-op
  touch does not.

The `toolchain` hash is stored once at the top of the manifest. A mismatch
against the current toolchain marks **every** module dirty (case 4 above),
because a compiler change can alter any beam. This matches the reality that
editing the elaborator invalidates the whole stdlib — correctly — and it is the
honest limit of the speedup: interface-level invalidation only avoids work
*within a fixed toolchain*.

The hash deliberately covers the **whole `:cure` application**, not a curated
"compiler-relevant" subset. That over-invalidates — editing an unrelated part of
the app (e.g. the REPL) also bumps the toolchain and rebuilds the stdlib — but
it is safe and needs no maintenance. A curated subset would be a fragile
allow-list that is easy to leave incomplete (a missed transitive dependency
would ship a stale beam), so the coarse-but-safe hash is the deliberate choice.

### Manifest

Stored alongside the output beams as `<output_dir>/.cure_manifest`, encoded with
`:erlang.term_to_binary/1` (no parser needed, fast). Shape:

```elixir
%{
  version: 1,                       # manifest schema version
  toolchain: <sha256 binary>,
  modules: %{
    "Std.List" => %{
      source_path: "lib/std/list.cure",
      source_hash: <sha256 binary>,
      interface_hash: <sha256 binary>,
      deps: ["Std.Core", ...],      # direct dependency module names, from DepGraph
      beams: ["Cure.Std.List.beam"] # every output file this source produced
    },
    ...
  }
}
```

Writes are **atomic**: serialize to `<output_dir>/.cure_manifest.tmp`, then
`File.rename/2` over the real path, so an interrupted build cannot leave a
half-written manifest. A manifest that is absent, unreadable, or fails to decode
to the expected shape/version is treated as empty → full rebuild (fail-safe:
the failure mode is *rebuild everything*, never *serve stale*).

### The incremental driver: `Cure.Compiler.Incremental`

A new module, the single place both mix tasks route through.

`compile_dir(source_paths, output_dir, opts) :: {:ok, summary} | {:error, ...}`

Steps:

1. **Scan** the sources with `Cure.Compiler.DepGraph.scan/1` +
   `order/1` (topological order) and `order_deps_map/1` (module → direct deps).
   Report import cycles exactly as the current task does.
2. **Load** the manifest (or empty on miss/corruption).
3. **Toolchain check.** If `manifest.toolchain != current_toolchain`, every
   module is dirty; skip to step 6 with `all_dirty = true`.
4. **Deletions.** For each module in the manifest whose `source_path` no longer
   exists among the scanned sources: delete its `beams`, drop it from the
   manifest. (A removed stdlib module must not leave an orphaned beam.)
5. **Single topological pass** to decide the dirty set. Dependencies are read
   from this build's freshly-scanned `order_deps_map/1` (not the manifest's
   stored `deps`), so a changed import set is always honoured — though a module
   whose imports changed also has a changed `source_hash` and is dirty anyway.
   Walking modules in dependency order, mark `M` dirty iff:
   - `source_hash(M)` differs from the manifest, or
   - `M` is new (absent from the manifest), or
   - any beam in `manifest[M].beams` is missing on disk, or
   - any direct dependency of `M` was recompiled this build *and* its new
     `interface_hash` differs from its stored one. A dependency with no stored
     `interface_hash` (new, or previously errored) counts as changed.

   Because deps precede dependents in topological order, each dependency's new
   `interface_hash` is known before its dependents are considered — no fixpoint
   loop is needed.
6. **Compile** the dirty modules, in topological order, via the existing
   `Cure.Compiler.compile_file/2`. For each success, recompute its
   `interface_hash` (from the same interface computation the elaborator already
   runs) and stage the updated manifest entry. On a compile **error**, do **not**
   stage an entry for that module — it stays dirty next run — and propagate the
   error the way the current task does (report + non-zero exit).
7. **Write** the updated manifest atomically (only if no compile errored, so a
   failed build never records partial freshness as complete).
8. Return a summary: counts of `compiled`, `skipped_fresh`, `deleted`, and any
   errors, for the task to print.

`opts`:
- `:force` (also `CURE_FULL_REBUILD=1` env) → skip steps 2-5, mark all dirty,
  clean rebuild. The escape hatch for a suspicious build.
- `:output_dir` default `_build/cure/ebin` (unchanged).

Interface-hash recomputation reuses the loader's existing interface computation
via `Cure.Elab.Program.module_interface/2` (see the fingerprint section for the
cache-sharing argument that keeps this off the second-elaboration path on full
builds).

### Mix task integration

- `Mix.Tasks.Cure.CompileStdlib` calls `Incremental.compile_dir` over
  `lib/std/*.cure`. Its output messages change from "Compiling … (81 modules)"
  to reporting compiled/skipped counts.
- `Mix.Tasks.Cure.Compile` (project builds) calls the same driver over the
  supplied sources.
- `test/test_helper.exs` is **unchanged** — it invokes the task and inherits the
  speedup. Its post-compile stickiness + declared-vs-loaded completeness checks
  (`test_helper.exs:35-120`) stay in place as an integration backstop: if the
  driver ever wrongly skipped a module, those checks raise loudly rather than
  letting a consumer flake. (They guard *presence*, not staleness, so they are a
  backstop, not the primary correctness mechanism — the fingerprints are.)

The `compile` alias in `mix.exs:135`
(`compile → cure.bundle_stdlib → cure.compile_stdlib → cure.bundle_stdlib_beams
→ cure.escript`) is left as-is; `cure.compile_stdlib` simply becomes cheap on a
no-op build. (The escript rebuild is a separate cost; not addressed here.)

### In-process `compile_and_load`

`Cure.Compiler.compile_and_load/2` (ad-hoc single-source compiles used directly
by tests) is **not** made incremental — there is nothing to cache for a
one-shot in-memory source. Incrementality applies to directory/project builds
only. This is the natural boundary of the feature.

## Correctness invariants (the part that must not regress)

1. **Never serve a stale beam.** Every channel by which a change reaches a
   module's output is a fingerprint input: its own source (`source_hash`), its
   dependencies' interfaces (`interface_hash`), and the compiler (`toolchain`).
2. **Beam presence is part of dirtiness** — a matching hash with a missing beam
   still recompiles.
3. **Only successful compiles update the manifest**, and the manifest is only
   written when the whole build succeeded — a failed or interrupted build never
   records partial freshness.
4. **Fail-safe on any manifest problem** — absent/corrupt/old-version manifest →
   full rebuild, never a skip.
5. **Determinism affects precision, not correctness.** If `export_env` carries
   run-varying data (fresh metavar/gensym counters), an identical recompile can
   yield a different `interface_hash`. That only over-invalidates dependents
   (safe, degrades toward module-level) and can never make two different envs
   collide. Skipped modules reuse their stored hash, so they are never affected.
   If over-invalidation proves noticeable in practice, a follow-up can normalize
   `export_env` before hashing; it is not required for correctness.

## Testing (red-green)

Unit tests for `Cure.Compiler.Incremental` over a temp-dir fixture of small
inter-dependent `.cure` modules (`A ← B ← C`, plus a private-helper module):

- **No change** → 0 recompiles.
- **Edit a leaf's source** → only that module recompiles.
- **Edit a dependency's exported definition** → the dependency *and* its
  transitive dependents recompile.
- **Edit a dependency's private/non-exported helper** (interface hash unchanged)
  → only that dependency recompiles; **no dependent rebuilds**. This is the test
  that proves interface-level actually buys something over module-level.
- **Toolchain hash bump** → all modules recompile.
- **Delete a source** → its beams are removed and it leaves the manifest.
- **Missing beam with matching source hash** → recompiles.
- **Corrupt / absent / wrong-version manifest** → full rebuild.
- **A module fails to compile** → it is not recorded fresh; the next build still
  treats it as dirty; the manifest is not advanced past the failure.
- **`force` / `CURE_FULL_REBUILD`** → rebuilds everything regardless of manifest.

Integration: the existing `test_helper.exs` stickiness + completeness checks and
`mix cure.check.stdlib` remain and must stay green. The full gate (this touches
the compile pipeline) runs with Antigen.

## Follow-ups (not in this spec)

- **Per-consumed-symbol invalidation** — finer than per-module interface;
  requires elaborator use-set instrumentation. Deferred (see scope note above).
- **`export_env` normalization** — only if determinism-driven over-invalidation
  is measured to matter.
- **Escript rebuild staleness** — the `cure.escript` step in the compile alias
  is a separate fixed cost not addressed here.
