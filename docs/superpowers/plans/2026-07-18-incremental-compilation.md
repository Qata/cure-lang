# Incremental Cure Compilation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make multi-file Cure builds recompile only modules whose output could differ, using content fingerprints + interface-level (Swift-style) invalidation, as a general compiler feature.

**Architecture:** A new `Cure.Compiler.Incremental` driver sits between "list of source files" and "compile each file". It uses `Cure.Compiler.DepGraph` for topological order and direct-dependency edges, a `Cure.Compiler.BuildManifest` for the persisted fingerprint store, and a new public `Cure.Elab.Program.module_interface/2` to obtain each module's `export_env` (the exact artifact consumers elaborate against) for interface hashing. Both `mix cure.compile_stdlib` and `mix cure.compile` route through the driver; `test/test_helper.exs` inherits the speedup unchanged.

**Tech Stack:** Elixir, ExUnit, `:crypto.hash/2`, `:erlang.term_to_binary/2`, existing `Cure.Compiler.{DepGraph, compile_file}` and `Cure.Elab.Program`.

## Global Constraints

- Compile Cure with OTP 26–28 (host compiler unaffected by AtomVM limits).
- Never co-sign commits — author as the user only.
- `lib/cure/elab/program.ex` and `lib/cure/core/*` are TCB: run the full gate (`mix test`, expect Antigen 318/318 and 0 failures) for any task touching them. TCB changes are pre-approved only when aligned with Idris/Agda/Lean; the changes here are build-infrastructure (a public accessor), not kernel semantics.
- Author stdlib in `lib/std/`; `priv/std` is generated — do not edit.
- Correctness rule that must never regress: **never serve a stale beam.** Every failure mode (absent/corrupt manifest, missing beam, compile error, non-serializable env) must fall back to *recompile*, never to *skip*.
- Fingerprints are content-based (`:crypto.hash(:sha256, ...)`), never mtime.
- Default `output_dir` is `_build/cure/ebin` everywhere.

---

## File Structure

- **Create** `lib/cure/compiler/build_manifest.ex` — `Cure.Compiler.BuildManifest`: the fingerprint store (load/save/atomic-write, empty, toolchain fingerprint). No compile logic.
- **Create** `lib/cure/compiler/incremental.ex` — `Cure.Compiler.Incremental`: the dirty-set computation + compile driver. Depends on `BuildManifest`, `DepGraph`, `Cure.Compiler`, `Cure.Elab.Program`.
- **Modify** `lib/cure/elab/program.ex` — add public `module_interface/2` wrapping the existing private `cached_module_interface/2`.
- **Modify** `lib/mix/tasks/cure.compile_stdlib.ex` — route through `Incremental.compile_dir/3`.
- **Modify** `lib/mix/tasks/cure.compile.ex` — route through `Incremental.compile_dir/3` for directory builds.
- **Create** `test/cure/compiler/build_manifest_test.exs` — manifest unit tests (`async: true`).
- **Create** `test/cure/compiler/incremental_test.exs` — driver tests over a temp-dir fixture (`async: false`; writes beams to a temp output dir + calls the real compiler).

---

## Task 1: Public interface accessor on the loader

Expose the loader's per-module interface (which carries `export_env` and the already-computed `source_hash`) so the driver can hash it. This is the only TCB-file change and it is purely additive.

**Files:**
- Modify: `lib/cure/elab/program.ex` (add public function near the existing private `cached_module_interface/2` at ~line 1441)
- Test: `test/cure/elab/module_interface_test.exs` (Create)

**Interfaces:**
- Produces: `Cure.Elab.Program.module_interface(module_name :: String.t(), path :: String.t()) :: {:ok, map()} | {:error, term()}`. The map includes at least `:export_env`, `:source_hash` (a 32-byte binary), `:dependency_names`, `:module_name`, `:path`. Semantics identical to the private `cached_module_interface/2`: `:persistent_term`-cached for stdlib paths, recomputed for others.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/module_interface_test.exs
defmodule Cure.Elab.ModuleInterfaceTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "module_interface/2 returns the export_env and source_hash for a stdlib module" do
    path = "lib/std/core.cure"
    assert {:ok, iface} = Program.module_interface("Std.Core", path)
    assert is_map(iface.export_env)
    assert is_binary(iface.source_hash) and byte_size(iface.source_hash) == 32
  end

  test "module_interface/2 is a cache hit on the second call (same term)" do
    path = "lib/std/core.cure"
    assert {:ok, a} = Program.module_interface("Std.Core", path)
    assert {:ok, b} = Program.module_interface("Std.Core", path)
    # stdlib interfaces are persistent_term-cached, so the cached tuple is reused
    assert :erts_debug.same(a, b)
  end

  test "module_interface/2 surfaces an error for a missing file" do
    assert {:error, _} = Program.module_interface("Nope", "lib/std/does_not_exist.cure")
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/module_interface_test.exs`
Expected: FAIL with `UndefinedFunctionError` for `Cure.Elab.Program.module_interface/2`.

- [ ] **Step 3: Add the public function**

In `lib/cure/elab/program.ex`, immediately above `defp cached_module_interface(module_name, path) do` (~line 1441), add:

```elixir
@doc """
Return the canonical module interface for `module_name` at `path`.

The interface map carries the elaborated `:export_env` a consumer merges in
when it imports this module, plus its `:source_hash`. This is the exact
artifact incremental compilation hashes to decide whether a change to this
module can affect its dependents. Semantics match the internal loader cache:
`:persistent_term`-cached for stdlib paths, recomputed otherwise.
"""
@spec module_interface(String.t(), String.t()) :: {:ok, map()} | {:error, term()}
def module_interface(module_name, path) when is_binary(module_name) and is_binary(path) do
  cached_module_interface(module_name, path)
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/module_interface_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Run the full gate (TCB file touched)**

Run: `mix test`
Expected: 0 failures; `Antigen shape-coverage: 318/318`.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/elab/program.ex test/cure/elab/module_interface_test.exs
git commit -m "feat(elab): expose module_interface/2 for incremental compilation"
```

---

## Task 2: `BuildManifest` — fingerprint store

The persisted fingerprint store plus the toolchain fingerprint. No compile logic; pure data + IO.

**Files:**
- Create: `lib/cure/compiler/build_manifest.ex`
- Test: `test/cure/compiler/build_manifest_test.exs`

**Interfaces:**
- Consumes: nothing from earlier tasks.
- Produces:
  - `@type entry :: %{source_path: String.t(), source_hash: binary(), interface_hash: binary() | nil, deps: [String.t()], beams: [String.t()]}`
  - `@type t :: %{version: pos_integer(), toolchain: binary(), modules: %{String.t() => entry()}}`
  - `Cure.Compiler.BuildManifest.empty(toolchain :: binary()) :: t()`
  - `Cure.Compiler.BuildManifest.load(output_dir :: String.t()) :: t()` — returns a fresh empty manifest (with `toolchain: ""`) on any read/decode/shape problem.
  - `Cure.Compiler.BuildManifest.save(manifest :: t(), output_dir :: String.t()) :: :ok` — atomic (temp file + rename).
  - `Cure.Compiler.BuildManifest.toolchain_fingerprint() :: binary()` — SHA-256 over the `:cure` app's compiled `.beam` files.
  - `@manifest_version 1` and the on-disk filename `.cure_manifest`.

- [ ] **Step 1: Write the failing tests**

```elixir
# test/cure/compiler/build_manifest_test.exs
defmodule Cure.Compiler.BuildManifestTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.BuildManifest, as: M

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_manifest_test_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "load/1 on an empty dir returns an empty manifest", %{dir: dir} do
    m = M.load(dir)
    assert m.version == 1
    assert m.modules == %{}
  end

  test "save/1 then load/1 round-trips", %{dir: dir} do
    m = %{
      version: 1,
      toolchain: <<1, 2, 3>>,
      modules: %{
        "Std.List" => %{
          source_path: "lib/std/list.cure",
          source_hash: <<9>>,
          interface_hash: <<8>>,
          deps: ["Std.Core"],
          beams: ["Cure.Std.List.beam"]
        }
      }
    }

    assert :ok = M.save(m, dir)
    assert M.load(dir) == m
  end

  test "load/1 on a corrupt manifest returns empty, never raises", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), "not a term <<<")
    assert M.load(dir).modules == %{}
  end

  test "load/1 on a wrong-version manifest returns empty", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), :erlang.term_to_binary(%{version: 999, toolchain: "", modules: %{}}))
    assert M.load(dir).modules == %{}
  end

  test "save/1 is atomic — no .tmp file is left behind", %{dir: dir} do
    assert :ok = M.save(M.empty(<<0>>), dir)
    refute File.exists?(Path.join(dir, ".cure_manifest.tmp"))
  end

  test "toolchain_fingerprint/0 is a stable 32-byte digest" do
    a = M.toolchain_fingerprint()
    b = M.toolchain_fingerprint()
    assert is_binary(a) and byte_size(a) == 32
    assert a == b
  end
end
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/cure/compiler/build_manifest_test.exs`
Expected: FAIL — `Cure.Compiler.BuildManifest` undefined.

- [ ] **Step 3: Implement `BuildManifest`**

```elixir
# lib/cure/compiler/build_manifest.ex
defmodule Cure.Compiler.BuildManifest do
  @moduledoc """
  Persisted fingerprint store for incremental Cure compilation.

  One manifest per output directory (`<output_dir>/.cure_manifest`), holding the
  compiler `toolchain` fingerprint and, per module, its content `source_hash`,
  `interface_hash`, direct `deps`, and the `beams` it produced. Any read or
  decode problem yields an empty manifest so the caller rebuilds everything —
  the failure mode is always "recompile", never "serve stale".
  """

  @manifest_version 1
  @filename ".cure_manifest"

  @type entry :: %{
          source_path: String.t(),
          source_hash: binary(),
          interface_hash: binary() | nil,
          deps: [String.t()],
          beams: [String.t()]
        }
  @type t :: %{version: pos_integer(), toolchain: binary(), modules: %{String.t() => entry()}}

  @spec empty(binary()) :: t()
  def empty(toolchain) when is_binary(toolchain),
    do: %{version: @manifest_version, toolchain: toolchain, modules: %{}}

  @spec load(String.t()) :: t()
  def load(output_dir) do
    path = Path.join(output_dir, @filename)

    with {:ok, bin} <- File.read(path),
         {:ok, term} <- safe_decode(bin),
         %{version: @manifest_version, toolchain: tc, modules: mods}
         when is_binary(tc) and is_map(mods) <- term do
      term
    else
      _ -> empty("")
    end
  end

  @spec save(t(), String.t()) :: :ok
  def save(manifest, output_dir) do
    File.mkdir_p!(output_dir)
    final = Path.join(output_dir, @filename)
    tmp = final <> ".tmp"
    File.write!(tmp, :erlang.term_to_binary(manifest))
    File.rename!(tmp, final)
    :ok
  end

  @doc "SHA-256 over the :cure application's compiled .beam files, in sorted path order."
  @spec toolchain_fingerprint() :: binary()
  def toolchain_fingerprint do
    beams =
      :cure
      |> Application.app_dir("ebin")
      |> Path.join("*.beam")
      |> Path.wildcard()
      |> Enum.sort()

    ctx = :crypto.hash_init(:sha256)

    beams
    |> Enum.reduce(ctx, fn beam, acc ->
      :crypto.hash_update(acc, File.read!(beam))
    end)
    |> :crypto.hash_final()
  end

  defp safe_decode(bin) do
    {:ok, :erlang.binary_to_term(bin, [:safe])}
  rescue
    _ -> :error
  end
end
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/compiler/build_manifest_test.exs`
Expected: PASS (6 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/build_manifest.ex test/cure/compiler/build_manifest_test.exs
git commit -m "feat(compiler): add BuildManifest fingerprint store for incremental builds"
```

---

## Task 3: Verify `export_env` is hashable, add the interface-hash helper

Confirm the serializability assumption on a real stdlib `export_env` and add the hashing helper to the driver module (created here, filled out in Task 4).

**Files:**
- Create: `lib/cure/compiler/incremental.ex` (module skeleton + `interface_hash/1`)
- Test: `test/cure/compiler/incremental_hash_test.exs`

**Interfaces:**
- Consumes: `Cure.Elab.Program.module_interface/2` (Task 1).
- Produces: `Cure.Compiler.Incremental.interface_hash(export_env :: map()) :: binary()` — 32-byte SHA-256 of the deterministically-serialized env.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/incremental_hash_test.exs
defmodule Cure.Compiler.IncrementalHashTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Incremental
  alias Cure.Elab.Program

  test "a real stdlib export_env is serializable and hashes deterministically" do
    {:ok, iface} = Program.module_interface("Std.Core", "lib/std/core.cure")
    h1 = Incremental.interface_hash(iface.export_env)
    h2 = Incremental.interface_hash(iface.export_env)
    assert is_binary(h1) and byte_size(h1) == 32
    assert h1 == h2
  end

  test "different envs hash differently" do
    {:ok, core} = Program.module_interface("Std.Core", "lib/std/core.cure")
    {:ok, list} = Program.module_interface("Std.List", "lib/std/list.cure")
    assert Incremental.interface_hash(core.export_env) != Incremental.interface_hash(list.export_env)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/compiler/incremental_hash_test.exs`
Expected: FAIL — `Cure.Compiler.Incremental` undefined.

- [ ] **Step 3: Create the module skeleton + `interface_hash/1`**

```elixir
# lib/cure/compiler/incremental.ex
defmodule Cure.Compiler.Incremental do
  @moduledoc """
  Interface-level incremental driver for multi-file Cure builds.

  Recompiles a module only when its source content changed, one of its output
  beams is missing, a direct dependency's interface changed, or the compiler
  itself changed. See `docs/superpowers/specs/2026-07-18-incremental-compilation-design.md`.
  """

  @doc """
  SHA-256 of a module's elaborated `export_env` — the exact artifact consumers
  merge in. If two versions of a module produce a byte-identical `export_env`,
  no consumer's compilation can differ, so its dependents need not recompile.
  """
  @spec interface_hash(map()) :: binary()
  def interface_hash(export_env) do
    :crypto.hash(:sha256, :erlang.term_to_binary(export_env, [:deterministic]))
  end
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/compiler/incremental_hash_test.exs`
Expected: PASS (2 tests).

**If Step 4 fails with an `ArgumentError` from `term_to_binary`** (env holds a live closure/pid/ref — not expected, but the spec's fallback): change `interface_hash/1` to hash a structural projection instead, replacing the body with:

```elixir
  def interface_hash(export_env) do
    projection = Map.take(export_env, [:defs, :families, :ctors, :ctor_to_family, :constrained])
    :crypto.hash(:sha256, :erlang.term_to_binary(projection, [:deterministic]))
  end
```

Re-run Step 4. (Use the field names actually present on the `Cure.Core.Env` struct — confirm against `lib/cure/core/inductive.ex`.)

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/incremental.ex test/cure/compiler/incremental_hash_test.exs
git commit -m "feat(compiler): add interface_hash over the elaborated export_env"
```

---

## Task 4: The dirty-set computation + compile driver

The core of the feature: `compile_dir/3`. Pure decision logic (dirty set) plus the compile loop and manifest update.

**Files:**
- Modify: `lib/cure/compiler/incremental.ex`
- Test: `test/cure/compiler/incremental_test.exs`

**Interfaces:**
- Consumes: `Cure.Compiler.BuildManifest` (Task 2), `Cure.Compiler.Incremental.interface_hash/1` (Task 3), `Cure.Elab.Program.module_interface/2` (Task 1), `Cure.Compiler.DepGraph.{scan/1, order/1, order_deps_map/1}`, `Cure.Compiler.compile_file/2` (returns `{:ok, module, warnings}` | `{:error, reason}`).
- Produces:
  - `Cure.Compiler.Incremental.compile_dir(source_paths :: [String.t()], output_dir :: String.t(), opts :: keyword()) :: {:ok, summary()} | {:error, term()}`
  - `@type summary :: %{compiled: [String.t()], skipped: [String.t()], deleted: [String.t()], errors: [{String.t(), term()}]}`
  - `opts`: `:force` (boolean) — also honored via `System.get_env("CURE_FULL_REBUILD")`.

**Design notes for the implementer (read before coding):**

- **Topological order** comes from `DepGraph.order/1`, which returns `{:ok, ordered_paths, cycles}`. **Direct dependency edges by module name** come from `DepGraph.order_deps_map/1` (`%{module => [dep_module_names]}`). Map each ordered path to its module name via the graph's `modules` inverse (`%{module => path}` — invert it once).
- A module produces potentially several beams (a `mod` plus lifted submodules). The **actual beam filenames** for a source are not known until it compiles. Record them from the output dir: after compiling source `P`, the beams it produced are the `Cure.*.beam` files in `output_dir` whose mtime is `>=` the moment before compiling `P`. Simpler and robust: snapshot `Path.wildcard(output_dir <> "/*.beam")` into a set *before* compiling `P`, and again *after*; the new/rewritten files are `P`'s beams. (Rewrites: compare content is overkill — treat any file present-after that was compiled this step as belonging to the just-compiled module. Since modules compile one at a time in order, the delta is attributable.) Store these names in the manifest entry so the *missing-beam* check has something to test.
- **Interface hash timing:** after successfully compiling module `M`, if `M` has ≥1 dependent in the set, call `Program.module_interface(M.module_name, M.path)` and `interface_hash/1` on its `export_env`; store it. This primes the loader cache the dependents will hit. If `M` has no dependents, store `interface_hash: nil` (nothing can cascade from it).
- **Dirty predicate**, evaluated in topological order (so each dep's fresh interface hash is known first). `M` is dirty iff any of:
  - `manifest.modules[M]` is absent (new), or
  - `source_hash(M) != manifest.modules[M].source_hash`, or
  - any beam in `manifest.modules[M].beams` is missing from disk, or
  - some direct dep `D` of `M` was recompiled this build and `new_interface_hash[D] != manifest.modules[D].interface_hash` (a `D` with no stored hash counts as changed).
- **Full-rebuild triggers** (mark every module dirty, skip the per-module predicate): `opts[:force]` or `CURE_FULL_REBUILD` set, or `manifest.toolchain != current_toolchain`.
- **Deletions:** any module in `manifest.modules` whose `source_path` is not among the scanned sources → `File.rm` its `beams`, exclude from the new manifest, add to `summary.deleted`.
- **Failure handling:** if `compile_file` returns `{:error, reason}`, add `{module, reason}` to `summary.errors`, do **not** add a manifest entry for it, and do **not** advance it. Continue compiling the rest (so one bad module does not hide others), but **do not write the manifest** if `summary.errors != []` — return `{:ok, summary}` with errors populated and let the task decide the exit code. This guarantees a failed build never records partial freshness.
- **Manifest write:** only when `summary.errors == []`. Build the new manifest from: fresh entries for compiled modules, carried-over entries for skipped modules, minus deleted ones, with `toolchain: current_toolchain`. Then `BuildManifest.save/2`.

- [ ] **Step 1: Write the failing tests**

```elixir
# test/cure/compiler/incremental_test.exs
defmodule Cure.Compiler.IncrementalTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{BuildManifest, Incremental}

  # A tiny 3-module chain: Leaf <- Mid <- Top, plus a private helper in Leaf.
  # `use` gives the import edges DepGraph reads.
  @leaf_v1 """
  mod Leaf do
    def pubval() : Int = helper()
    def helper() : Int = 1
  end
  """

  # same public surface, different PRIVATE helper body -> interface unchanged
  @leaf_v2_private """
  mod Leaf do
    def pubval() : Int = helper()
    def helper() : Int = 2
  end
  """

  # changed PUBLIC surface -> interface changed
  @leaf_v3_public """
  mod Leaf do
    def pubval() : Int = 7
    def helper() : Int = 1
  end
  """

  @mid """
  mod Mid do
    use Leaf
    def midval() : Int = pubval()
  end
  """

  @top """
  mod Top do
    use Mid
    def topval() : Int = midval()
  end
  """

  setup do
    root = Path.join(System.tmp_dir!(), "cure_incr_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    File.mkdir_p!(out)
    on_exit(fn -> File.rm_rf!(root) end)

    write = fn name, body -> File.write!(Path.join(src, name), body) end
    write.("leaf.cure", @leaf_v1)
    write.("mid.cure", @mid)
    write.("top.cure", @top)

    paths = Path.wildcard(Path.join(src, "*.cure"))
    {:ok, src: src, out: out, paths: paths, write: write}
  end

  defp compile(paths, out, opts \\ []), do: Incremental.compile_dir(paths, out, opts)

  test "first build compiles every module", %{paths: paths, out: out} do
    assert {:ok, s} = compile(paths, out)
    assert Enum.sort(s.compiled) == ["Leaf", "Mid", "Top"]
    assert s.skipped == []
  end

  test "no-change rebuild compiles nothing", %{paths: paths, out: out} do
    assert {:ok, _} = compile(paths, out)
    assert {:ok, s} = compile(paths, out)
    assert s.compiled == []
    assert Enum.sort(s.skipped) == ["Leaf", "Mid", "Top"]
  end

  test "editing a leaf's PRIVATE helper recompiles only the leaf", %{paths: paths, out: out, src: src, write: write} do
    assert {:ok, _} = compile(paths, out)
    write.("leaf.cure", @leaf_v2_private)
    assert {:ok, s} = compile(paths, out)
    assert s.compiled == ["Leaf"]
    assert Enum.sort(s.skipped) == ["Mid", "Top"]
    _ = src
  end

  test "editing a leaf's PUBLIC surface cascades to dependents", %{paths: paths, out: out, write: write} do
    assert {:ok, _} = compile(paths, out)
    write.("leaf.cure", @leaf_v3_public)
    assert {:ok, s} = compile(paths, out)
    assert Enum.sort(s.compiled) == ["Leaf", "Mid", "Top"]
  end

  test "a missing beam forces recompile even when the hash matches", %{paths: paths, out: out} do
    assert {:ok, _} = compile(paths, out)
    File.rm!(Path.join(out, "Cure.Leaf.beam"))
    assert {:ok, s} = compile(paths, out)
    assert "Leaf" in s.compiled
  end

  test "a toolchain change forces a full rebuild", %{paths: paths, out: out} do
    assert {:ok, _} = compile(paths, out)
    # Corrupt the stored toolchain so it mismatches the current fingerprint.
    m = BuildManifest.load(out)
    BuildManifest.save(%{m | toolchain: <<0>>}, out)
    assert {:ok, s} = compile(paths, out)
    assert Enum.sort(s.compiled) == ["Leaf", "Mid", "Top"]
  end

  test "deleting a source removes its beam and drops it from the manifest", %{paths: paths, out: out, src: src} do
    assert {:ok, _} = compile(paths, out)
    File.rm!(Path.join(src, "top.cure"))
    remaining = Path.wildcard(Path.join(src, "*.cure"))
    assert {:ok, s} = compile(remaining, out)
    assert "Top" in s.deleted
    refute File.exists?(Path.join(out, "Cure.Top.beam"))
    refute Map.has_key?(BuildManifest.load(out).modules, "Top")
  end

  test "a compile error keeps the module dirty and does not advance the manifest", %{paths: paths, out: out, write: write} do
    assert {:ok, _} = compile(paths, out)
    write.("leaf.cure", "mod Leaf do\n  def pubval() : Int = nonexistent_fn()\nend\n")
    assert {:ok, s} = compile(paths, out)
    assert [{"Leaf", _}] = s.errors
    # manifest NOT advanced: next run still sees Leaf as dirty
    assert {:ok, s2} = compile(paths, out)
    assert "Leaf" in (s2.compiled ++ Enum.map(s2.errors, &elem(&1, 0)))
  end

  test "force rebuilds everything", %{paths: paths, out: out} do
    assert {:ok, _} = compile(paths, out)
    assert {:ok, s} = compile(paths, out, force: true)
    assert Enum.sort(s.compiled) == ["Leaf", "Mid", "Top"]
  end
end
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/cure/compiler/incremental_test.exs`
Expected: FAIL — `compile_dir/3` undefined.

- [ ] **Step 3: Implement `compile_dir/3` and its helpers**

Add to `lib/cure/compiler/incremental.ex` (alongside `interface_hash/1`). Implement per the Design notes above. Reference skeleton:

```elixir
  alias Cure.Compiler.{BuildManifest, DepGraph}
  alias Cure.Elab.Program

  @type summary :: %{
          compiled: [String.t()],
          skipped: [String.t()],
          deleted: [String.t()],
          errors: [{String.t(), term()}]
        }

  @spec compile_dir([String.t()], String.t(), keyword()) :: {:ok, summary()} | {:error, term()}
  def compile_dir(source_paths, output_dir, opts \\ []) do
    File.mkdir_p!(output_dir)

    # DepGraph.order/1 returns {:ok, ordered_paths, cycles}; treat a non-empty
    # `cycles` as a hard error, reported the way the current task does.
    with {:ok, graph} <- DepGraph.scan(source_paths),
         {:ok, ordered_paths, []} <- DepGraph.order(graph) do
      path_to_module = for {m, p} <- graph.modules, into: %{}, do: {p, m}
      deps_map = DepGraph.order_deps_map(graph)

      ordered_modules =
        ordered_paths
        |> Enum.map(&path_to_module[&1])
        |> Enum.reject(&is_nil/1)

      manifest = BuildManifest.load(output_dir)
      toolchain = BuildManifest.toolchain_fingerprint()
      force? = Keyword.get(opts, :force, false) or System.get_env("CURE_FULL_REBUILD") not in [nil, ""]
      full_rebuild? = force? or manifest.toolchain != toolchain

      deleted = deleted_modules(manifest, ordered_modules)
      Enum.each(deleted, fn m -> Enum.each(manifest.modules[m].beams, &rm_beam(output_dir, &1)) end)

      state = %{
        output_dir: output_dir,
        graph: graph,
        deps_map: deps_map,
        path_to_module: path_to_module,
        old: manifest.modules,
        new: %{},
        iface: %{},        # module => fresh interface_hash (or nil)
        recompiled: MapSet.new(),
        summary: %{compiled: [], skipped: [], deleted: deleted, errors: []}
      }

      state = Enum.reduce(ordered_modules, state, fn m, st ->
        process_module(m, st, full_rebuild?)
      end)

      if state.summary.errors == [] do
        BuildManifest.save(%{version: 1, toolchain: toolchain, modules: state.new}, output_dir)
      end

      {:ok, finalize_summary(state.summary)}
    end
  end
```

Then implement the helpers referenced above (`deleted_modules/2`; `rm_beam/2`; `process_module/3` doing the dirty predicate, the compile via `Cure.Compiler.compile_file/2`, the before/after beam-set diff, the interface-hash priming, and the manifest-entry construction; `finalize_summary/1` to sort lists). Follow the Design notes exactly — especially: dirty predicate in topo order, interface hash only for modules with dependents, no manifest entry on error, and beam-set-diff for the `beams` field. Compute `source_hash` as `:crypto.hash(:sha256, File.read!(path))`.

A module `M` "has a dependent" iff some other in-set module lists `M` in `deps_map`. Precompute a reverse map once.

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/compiler/incremental_test.exs`
Expected: PASS (10 tests). If the private-helper test fails (Leaf recompiles Mid/Top), the interface hash is picking up private-helper changes — inspect what `export_env` includes for a non-exported def; if private defs genuinely appear in `export_env`, this is expected behavior for this language and the test's premise is wrong: adjust the test to use a change that is provably interface-invariant (e.g. reordering two independent public defs, or a comment/whitespace change) and note the finding in the commit message.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/incremental.ex test/cure/compiler/incremental_test.exs
git commit -m "feat(compiler): interface-level incremental compile driver"
```

---

## Task 5: Route the stdlib task through the driver

**Files:**
- Modify: `lib/mix/tasks/cure.compile_stdlib.ex`
- Test: reuse `test/cure/stdlib/*` + `mix cure.check.stdlib` (integration); no new unit test file (the task is a thin wrapper the driver tests already cover).

**Interfaces:**
- Consumes: `Cure.Compiler.Incremental.compile_dir/3`.

- [ ] **Step 1: Replace the compile loop**

In `lib/mix/tasks/cure.compile_stdlib.ex`, replace the `Enum.map(cure_files, ...)` compile block (the `true ->` branch body, ~lines 61-100) with a call to the driver over the ordered files, preserving the error-exit behavior:

```elixir
      true ->
        File.mkdir_p!(output_dir)
        abs_dir = Path.expand(output_dir)
        unless abs_dir in :code.get_path(), do: :code.add_patha(String.to_charlist(abs_dir))

        case Cure.Compiler.Incremental.compile_dir(cure_files, output_dir, []) do
          {:ok, summary} ->
            Mix.shell().info(
              "  #{length(summary.compiled)} compiled, " <>
                "#{length(summary.skipped)} up-to-date, " <>
                "#{length(summary.deleted)} removed"
            )

            Mix.shell().info("  Output: #{output_dir}")

            unless summary.errors == [] do
              Enum.each(summary.errors, fn {mod, reason} ->
                Mix.shell().error("  #{mod}: #{Cure.Compiler.Errors.format_error(reason, mod)}")
              end)

              exit({:shutdown, 1})
            end

          {:error, reason} ->
            Mix.shell().error(Cure.Compiler.Errors.format_error(reason, stdlib_dir))
            exit({:shutdown, 1})
        end
```

Note: `cure_files` is already the DepGraph-ordered list from the existing `scan`/`order` block above it; `compile_dir` re-scans internally, which is fine (idempotent) — or pass `cure_files` and let the driver own scanning. Keep the existing cycle-reporting block as-is.

- [ ] **Step 2: Verify stdlib still compiles clean**

Run: `mix cure.compile_stdlib`
Expected: `81 compiled, 0 up-to-date, 0 removed` on a cold build; run it **again** and expect `0 compiled, 81 up-to-date, 0 removed`.

- [ ] **Step 3: Verify the stdlib integrity checks still pass**

Run: `mix cure.check.stdlib`
Expected: passes (declared == compiled, no orphans).

- [ ] **Step 4: Commit**

```bash
git add lib/mix/tasks/cure.compile_stdlib.ex
git commit -m "perf(compiler): make cure.compile_stdlib incremental"
```

---

## Task 6: Route the project-compile task through the driver

**Files:**
- Modify: `lib/mix/tasks/cure.compile.ex`
- Test: reuse `test/cure/project/compile_project_test.exs` (integration).

**Interfaces:**
- Consumes: `Cure.Compiler.Incremental.compile_dir/3`.

- [ ] **Step 1: Route directory builds through the driver**

In `lib/mix/tasks/cure.compile.ex`, where a directory/wildcard expands to multiple `.cure` files (the `Path.wildcard() |> Enum.each(&compile_one/2)` branch, ~line 41), replace the per-file loop with:

```elixir
        files = Path.wildcard(path)

        case Cure.Compiler.Incremental.compile_dir(files, output_dir, []) do
          {:ok, summary} ->
            Mix.shell().info(
              "#{length(summary.compiled)} compiled, #{length(summary.skipped)} up-to-date"
            )

            unless summary.errors == [] do
              Enum.each(summary.errors, fn {mod, reason} ->
                Mix.shell().error("#{mod}: #{Cure.Compiler.Errors.format_error(reason, mod)}")
              end)

              exit({:shutdown, 1})
            end

          {:error, reason} ->
            Mix.shell().error(Cure.Compiler.Errors.format_error(reason, path))
            exit({:shutdown, 1})
        end
```

Leave the single-file path (`compile_one/2`) unchanged — a lone file has nothing to be incremental against.

- [ ] **Step 2: Run the project compile test**

Run: `mix test test/cure/project/compile_project_test.exs`
Expected: PASS.

- [ ] **Step 3: Commit**

```bash
git add lib/mix/tasks/cure.compile.ex
git commit -m "perf(compiler): make cure.compile directory builds incremental"
```

---

## Task 7: Full gate + wall-clock confirmation

**Files:** none (verification only).

- [ ] **Step 1: Run the full suite**

Run: `mix test`
Expected: 0 failures; `Antigen shape-coverage: 318/318`; the existing `test_helper` "stuck N canonical stdlib modules" line still prints.

- [ ] **Step 2: Confirm the incremental win on the test-loop path**

Run `mix test test/cure/compiler/build_manifest_test.exs` twice in a row (no source change between). The second run's `test_helper: compiling Cure stdlib` step should now report `0 compiled, 81 up-to-date` instead of recompiling all 81.

Expected observation: the pre-test stdlib step drops from ~7.5s to well under 1s on the no-change second run.

- [ ] **Step 3: Confirm CI still runs the whole suite**

Run: `mix test --include slow`
Expected: 0 failures (the `:slow` stdlib-scale tests still pass with incremental compilation underneath them).

- [ ] **Step 4: Update memory**

Update `suite-wallclock-optimization.md` and `MEMORY.md` with the incremental-compilation landing (fingerprint basis, interface-level via `export_env` hash, the toolchain-invalidates-everything limit, and the measured no-change stdlib-step time).

- [ ] **Step 5: Commit**

```bash
git add ../../../.claude/projects/*/memory/*.md 2>/dev/null || true
git commit -m "docs: record incremental compilation landing" || true
```

(Memory files live outside the repo; if `git add` finds nothing in-repo, this commit is a no-op — that is fine.)

---

## Self-Review Notes

- **Spec coverage:** fingerprints (Tasks 2, 3), manifest + atomic write + fail-safe (Task 2), toolchain hash (Task 2), dirty-set single topo pass (Task 4), interface hash via `module_interface/2` with cache-sharing (Tasks 1, 3, 4), deletions (Task 4), error-does-not-advance-manifest (Task 4), force/env bypass (Task 4), driver integration for stdlib + project (Tasks 5, 6), test_helper inherits unchanged (Task 5 verification), correctness invariants (Task 4 design notes + tests), testing matrix (Task 4). Per-consumed-symbol and export_env normalization are explicitly out of scope (spec follow-ups) — no task, correct.
- **Serializability risk** is handled by Task 3's verification step + inline fallback.
- **Private-vs-public interface** premise is verified by Task 4's private-helper test, with an explicit instruction to correct the test if `export_env` includes private defs in this language.
- **Type consistency:** `summary` shape, `entry`/`t` shapes, and `module_interface/2`/`interface_hash/1`/`compile_dir/3` signatures are used identically across tasks.
