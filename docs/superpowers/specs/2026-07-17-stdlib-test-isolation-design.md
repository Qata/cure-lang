# Deterministic, parallel-safe stdlib in the Cure test suite — Design

**Status:** approved (design gate), 2026-07-17
**Branch:** `autopilot/stdlib-test-isolation` (cut from `feature/idris-parity`)

## Problem

The Cure compiler emits every module as a real BEAM module loaded under its
**canonical global name** (`Cure.Std.Iter`, `Cure.Std.String`, …). The BEAM has
exactly one global code table — one slot per module name for the whole VM. Any
test that exercises the compiler end-to-end (elaborate → emit → `:code.load` →
call it) must install its module into that shared slot.

`test_helper` compiles the canonical, full stdlib once at startup. Then
individual **producer** tests emit *their own* version of some stdlib module and
load it under the same name, overwriting the canonical one for every later test.
The versions differ in two ways, both observed as live failures:

- **Pared-down surface** — a test tree-shakes and emits only the functions it
  needs, so its `Cure.Std.Map` is missing `get/2`. A later consumer calling
  `get/2` fails.
- **Different lowering** — a test emits a module with an older/different
  constructor lowering, so it returns `{:done}` where the canonical returns
  `:Done`, or leaks an `:Emit` effect atom into a runtime tuple.

Because loading a new version forces a purge of the old (BEAM keeps at most two
versions), "reload" mechanically means "purge + load," and the resident version
after a clobber is whatever the last producer installed.

This is **order-dependent contamination**: the failing files
(`test/cure/stdlib/iter_test.exs`, `test/cure/stdlib/stdlib_test.exs`) pass in
isolation (124/124) but fail in the full suite (a run showed 10 failures). It is
also *why* ~44 test files carry `async: false` — serialization is a band-aid
that reduces, but does not remove, the clobber.

The structural root is that `Cure.Elab.Emit.remote_target/2` (`emit.ex:195`)
lowers a cross-module call to a **hardcoded** remote target
(`{Cure.Std.Map, size}`) baked into the *caller*, so a callee must be loadable
under its exact canonical name. That hardcoded name forces every test onto the
same global slot.

## Goal

Make the suite **correct under parallelism** and keep it a **single suite**:
eliminate the clobber flakes and unlock `async: true` for the tests currently
forced serial by them. Non-goals: partitioning into multiple OS processes (a
sledgehammer we explicitly rejected in favor of the root fix), reducing test
count, or changing production compiler behavior.

## Architecture

Two complementary mechanisms plus carve-outs:

- **Stick the canonical stdlib** protects *consumers* — the majority that just
  call `Cure.Std.X.f`. Once the full canonical surface is resident and made
  sticky, nothing can overwrite it, so consumers always see the correct module.
- **Namespace the producers** isolates the *emitter-verifying* tests — those
  that deliberately emit their own version to assert on the emitter's output.
  Each producer's emitted group loads under a unique per-test prefix, so it
  never touches the canonical slot.

Sticky + namespacing compose: namespacing removes the producers' reason to touch
the shared slot; sticky is the enforcement that guarantees nothing ever
regresses the canonical and turns any missed producer into a loud, deterministic
`:sticky_directory` failure instead of a silent flake.

## Components

### C1 — Startup: load-all + stick (`test/test_helper.exs`)

After `Mix.Task.run("cure.compile_stdlib")`, enumerate every compiled canonical
stdlib beam, `:code.ensure_loaded` each, and `:code.stick_mod` each.

- **Source of the module list:** the beams `cure.compile_stdlib` writes to
  `_build/cure/ebin/Cure.*.beam` (the same glob `Cure.Stdlib.Preload` loads from
  at `preload.ex:592`). Module name = `Path.basename(path, ".beam") |> String.to_atom`.
- **Full-surface guarantee:** every module a consumer references must be loaded
  *before* sticking, or a consumer could still hit a not-loaded module. The
  implementation asserts the load set is non-empty and that a known sentinel set
  (`Cure.Std.String`, `Cure.Std.Core`, `Cure.Std.Iter`, `Cure.Std.Map`,
  `Cure.Std.List`) is present and loaded; a missing sentinel fails the suite at
  startup with a clear message rather than flaking later.
- **Safety under sticky:** `Cure.Stdlib.Preload.load_if_present/2`
  (`preload.ex:605`) already maps `{:error, _}` (including `:sticky_directory`)
  to `:ok`, so re-preload calls no-op instead of crashing. This is a
  precondition the plan verifies with a test, not an assumption.
- **Scope:** stick only `Cure.Std.*` (and any other canonical `Cure.*` stdlib
  module emitted by `compile_stdlib`). Never stick user/test-emitted modules.
- **Per-process:** sticking happens once per suite process; each `mix test`
  starts a fresh BEAM, so there is no cross-run state.

### C2 — Producer namespacing (`lib/cure/elab/emit.ex` + producer tests)

Thread an optional module-name **prefix** through the emit entry points so a
producer's whole emitted group is installed and cross-linked under that prefix.

- **`remote_target/2` → `remote_target/3`** (or an added prefix+local-owner
  argument): for an owner in the *locally emitted group*, target
  `{String.to_atom(prefix <> "Cure." <> owner), base}`; for an owner **not** in
  the emitted group, keep the bare canonical `{String.to_atom("Cure." <> owner),
  base}` so the call resolves to the sticky canonical. `:local` and
  `origins`-routed cases are unchanged except for prefixing local-group owners.
- **`compile_and_load/2` and `compile_forms/3`** accept `prefix` and
  `local_owners` (the set of owners being emitted in this call) in `opts`,
  default `prefix: ""` and `local_owners: <derived from functions>`. With the
  default empty prefix, byte-for-byte output is **identical** to today — this is
  the invariant that keeps golden tests and production compilation unchanged.
- **Producer tests** pass `prefix: prefix_for(__MODULE__)` where `prefix_for`
  sanitizes the module name into a valid atom-name segment (e.g.
  `Cure.Stdlib.SetDependentRunTest` → `T_Cure_Stdlib_SetDependentRunTest.`),
  and read back their module under the prefixed name.
- **Delegation faithfulness:** a producer that emits a group (e.g. Set + Map)
  passes the *whole* group's owners as `local_owners`, so Set's delegated call
  to Map lowers to `{Prefix.Cure.Std.Map, size}` and exercises the genuine
  cross-module remote-call path inside the sandbox — not a bundle-into-one-module
  shortcut (which the existing `set_dependent_run_test` comment explicitly warns
  against).

### C3 — Simplify pure consumers

Tests that emit/load their own stdlib module **only for historical safety** (not
to assert on emitter output) drop the emission and call the sticky canonical
directly. Identified by: the test does not assert on the *bytes/shape/name* of
the emitted artifact, only on runtime results that the canonical module also
produces.

### C4 — Golden carve-out

Tests that SHA-256 or byte-compare the compiled BEAM bake the module name into
the compared bytes (the actor-quote golden gate; `actor_family_raw`). These
verify **canonical** output and MUST stay un-namespaced (empty prefix). They may
remain `async: false`. Consequence stated honestly: "all async" is ~95%, not
100%.

### C5 — Reclassify to async

Once a producer is namespaced (C2) or simplified to a pure consumer (C3), and it
has no other genuine global-state reason (telemetry handlers, `Application`
env, cwd), flip it to `async: true`. Files with genuine non-clobber global state
(`telemetry_test`, `otel_test`, `observe_test`, `profiler_test`, most
`antigen/*` with shared coverage tallies) stay `async: false`.

## Baseline already landed

The Path B elaboration cache (`perf(elab): memoize module_slice_env by path`,
commit `0c36c631`) is the measured baseline: full suite ~22 min → ~6 min. It is
orthogonal to this work — keyed by source path at *elaboration* time, unaffected
by emit-time module names — and stays. This design is what makes that fast suite
trustworthy under parallelism.

## Data flow

1. Suite start: `compile_stdlib` writes `_build/cure/ebin/Cure.*.beam`; C1 loads
   + sticks them → canonical surface is resident and immutable.
2. Consumer test runs: calls `Cure.Std.X.f` → hits the sticky canonical. No
   emission, no clobber.
3. Producer test runs: emits its group under `prefix`, loads
   `Prefix.Cure.Std.X`, calls it. `remote_target` keeps intra-group calls
   prefixed and extra-group calls pointed at the sticky canonical. No canonical
   slot is touched.
4. A missed producer (still emitting a bare canonical name): its `load_binary`
   is refused with `:sticky_directory` → deterministic failure naming the file,
   converted from a silent flake into a worklist item.

## Error handling

- `:code.load_binary` of a stuck module → `{:error, :sticky_directory}`.
  Preload tolerates it (no-op). A producer using `{:ok, _} = compile_and_load`
  under a bare name will crash — that is the intended forcing function and is
  resolved by namespacing that producer, not by loosening sticky.
- Startup sentinel missing → fail the suite immediately with a message pointing
  at `compile_stdlib`.
- `prefix_for/1` must always yield a valid atom segment; an unexpected module
  name shape raises at emit time rather than producing a malformed module atom.

## Testing strategy

The suite is its own integration test; determinism is the property under test.

- **Preload-tolerates-sticky** (C1 precondition): a unit test sticks a throwaway
  module and asserts `load_if_present` returns `:ok` and does not raise.
- **Empty-prefix byte-identity** (C2 invariant): emit a fixed module with
  `prefix: ""` and assert the loaded module's exported functions and results
  match the pre-change canonical emission (guards production/golden unchanged).
- **Prefixed isolation** (C2): emit a stdlib group under two distinct prefixes
  in one process and assert both coexist, are independently callable, and do not
  clobber the canonical (canonical still returns its own results afterward).
- **Prefixed delegation** (C2): a namespaced Set+Map group's delegated call
  returns correct results, proving the intra-group remote target was prefixed.
- **Determinism gate:** run the full suite twice at two fixed seeds; zero
  failures both times. Before this work, the 10-failure run reproduces the
  clobber; after, both seeds are green.
- **Timing:** record wall-clock; expect ≤ the ~6 min Path B baseline, ideally
  lower as more files go async.

## Sequencing (also the falsification plan)

1. C1 sticky + full-load. Run the gate → the producer worklist appears as
   `:sticky_directory` failures. This also proves Path B never touched the
   clobber failures (they are a code-table layer, not elaboration).
2. C2 emit.ex prefix threading (empty-prefix byte-identity test first — red,
   then green — before any producer is migrated).
3. Migrate each producer on the worklist: namespace (C2) or simplify (C3).
4. C4 golden carve-out — confirm the byte-compare tests still pass un-namespaced.
5. C5 flip isolated files to async.
6. Determinism gate (two fixed seeds green) + timing.

## Risks

- **`emit.ex` is TCB-adjacent.** The kernel re-checks emitter output, but codegen
  changes still require the full gate. Empty-prefix byte-identity is the guard
  that the default path is untouched.
- **Incomplete canonical surface at startup.** If `compile_stdlib` does not emit
  a module a consumer needs, sticking cannot cover it. Mitigated by the sentinel
  assertion (C1).
- **Delegation tests short-circuiting.** If `local_owners` is set wrong, an
  intra-group call could hit the canonical instead of the sandbox, weakening the
  test. Mitigated by the prefixed-delegation test (C2).
- **Atom/code accumulation.** Each namespaced module is a new resident atom/module,
  never purged. Bounded (hundreds, small); negligible. Optional `on_exit` purge
  if it ever matters.
