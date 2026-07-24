defmodule Cure.Compiler.Incremental do
  @moduledoc """
  Interface-level incremental driver for multi-file Cure builds.

  Recompiles a module only when its source content changed, one of its output
  beams is missing, a direct dependency's interface changed, or the compiler
  itself changed. See `docs/superpowers/specs/2026-07-18-incremental-compilation-design.md`.
  """

  alias Cure.Compiler.{BuildManifest, DepGraph}
  alias Cure.Elab.Program

  @type summary :: %{
          compiled: [String.t()],
          skipped_fresh: [String.t()],
          deleted: [String.t()],
          errors: [{term(), term()}],
          cycles: [list()]
        }

  @doc """
  SHA-256 of a module's elaborated `export_env` — the exact artifact consumers
  merge in. If two versions of a module produce a byte-identical `export_env`,
  no consumer's compilation can differ, so its dependents need not recompile.
  """
  @spec interface_hash(Cure.Compiler.ModuleInterface.t() | map()) :: binary()
  def interface_hash(%Cure.Compiler.ModuleInterface{interface_hash: hash}), do: hash

  def interface_hash(export_env) do
    :crypto.hash(:sha256, :erlang.term_to_binary(export_env, [:deterministic]))
  end

  @spec compile_dir([Path.t()], String.t(), keyword()) :: {:ok, summary()} | {:error, term()}
  def compile_dir(source_paths, output_dir, opts \\ []) do
    File.mkdir_p!(output_dir)

    # Put the output dir on the code path so a module compiled earlier in the
    # walk is resolvable when a later `use`-dependent is codegen'd — the same
    # setup `mix cure.compile_stdlib` performs for its ordered build.
    abs_out = Path.expand(output_dir)

    unless String.to_charlist(abs_out) in :code.get_path() do
      :code.add_patha(String.to_charlist(abs_out))
    end

    case DepGraph.scan(source_paths) do
      {:error, reason} -> {:error, reason}
      {:ok, graph} -> run(graph, source_paths, output_dir, opts)
    end
  end

  @doc """
  SHA-256 over the stdlib beams a project build will actually link against,
  resolved via `Cure.Stdlib.Paths.beam_dir/0` — the stdlib's real on-disk
  location (`:stdlib_beam_dir` override, bundled `priv/ebin`, `$CURE_HOME`, or
  the `_build/cure/ebin` dev fallback), NOT the project's own `output_dir`.

  This is the fingerprint a project build stores and re-checks to decide whether
  the stdlib changed under it. Resolving the real beam dir (instead of the
  project's `output_dir`, which for a non-default `--output-dir` holds no stdlib
  beams) is what lets a project built to an unusual output dir still notice a
  stdlib change and rebuild. Returns the empty-list hash when no stdlib beam dir
  exists yet — a stable constant, so the first real stdlib compile moves it.
  """
  @spec stdlib_fingerprint() :: binary()
  def stdlib_fingerprint do
    case Cure.Stdlib.Paths.beam_dir() do
      nil -> stdlib_fingerprint_over([])
      dir -> stdlib_fingerprint(dir)
    end
  end

  @doc """
  SHA-256 over `Cure.Std.*.beam` content in a specific `dir`, sorted. Prefer the
  zero-arity `stdlib_fingerprint/0`, which resolves the stdlib's real beam
  location; this arity is for pointing at an explicit directory (tests, tools).
  """
  @spec stdlib_fingerprint(String.t()) :: binary()
  def stdlib_fingerprint(dir) do
    dir
    |> Path.join("Cure.Std.*.beam")
    |> Path.wildcard()
    |> stdlib_fingerprint_over()
  end

  defp stdlib_fingerprint_over(files) do
    files
    |> Enum.sort()
    |> Enum.reduce(:crypto.hash_init(:sha256), fn f, acc ->
      :crypto.hash_update(acc, File.read!(f))
    end)
    |> :crypto.hash_final()
  end

  @doc """
  Named modules in dependency-first compile order: every module appears AFTER all
  of its `use`-dependencies (`order_deps`). This is the only sound compile order —
  a module's codegen links its use-deps' beams, so those must be built first.

  Ordering follows the acyclic `order_deps` graph, NOT `closure_deps`. The closure
  superset adds ambient `@prelude`/qualified edges that make the primitive modules
  a single cycle (`Std.Atom`, `Std.Binary`, `Std.Char`, ...); a cyclic graph has
  no dependency-respecting order, and `toposort` would emit the cycle
  alphabetically — scheduling `Std.Binary` before `Std.Char` despite
  `Binary use Char`, which breaks a cold build. `order_deps` is also the *complete*
  compile dependency: the only cross-module beam a module links is a `use`-dep
  (a qualified call without `use` does not compile), so nothing load-bearing is
  lost by ignoring the closure-only edges here. Change propagation still uses the
  conservative closure superset — see `dep_changed?/2`.
  """
  @spec compile_order(DepGraph.t()) :: [String.t()]
  def compile_order(graph) do
    order = DepGraph.order_deps_map(graph)
    DepGraph.toposort(order, Map.keys(order))
  end

  defp run(graph, source_paths, output_dir, opts) do
    {:ok, _ordered, cycles} = DepGraph.order(graph)
    closure = DepGraph.closure_deps_map(graph)
    walk = compile_order(graph)
    prelude_providers = DepGraph.prelude_provider_names(graph)

    forced_paths =
      for {path, node} <- graph.nodes,
          not node.blank?,
          not is_binary(node.module),
          do: path

    force? =
      Keyword.get(opts, :force, false) or
        System.get_env("CURE_FULL_REBUILD") not in [nil, ""]

    toolchain = BuildManifest.toolchain_fingerprint()
    manifest = if force?, do: BuildManifest.empty(toolchain), else: BuildManifest.load(output_dir)

    stdlib_hash = Keyword.get(opts, :stdlib_hash, manifest.stdlib_hash)

    all_dirty? =
      force? or manifest.toolchain != toolchain or
        (Keyword.has_key?(opts, :stdlib_hash) and manifest.stdlib_hash != stdlib_hash)

    roots =
      opts
      |> Keyword.get(:source_roots, source_paths |> Enum.map(&Path.dirname/1) |> Enum.uniq())
      |> Enum.map(&Path.expand/1)

    {manifest, deleted} =
      if force?, do: {manifest, []}, else: delete_removed(manifest, roots, output_dir)

    # Base-dirtiness is independent of visit order: it depends only on a module's
    # own source bytes, its recorded beams, and the global rebuild flags. Compute
    # it up front so `dep_changed?/2` can consult a not-yet-visited closure dep
    # (only possible across an ambient `@prelude` cycle back-edge, where the walk
    # order cannot place the dep first) and still cascade soundly.
    base_dirty =
      for mod <- walk, into: %{} do
        path = Map.fetch!(graph.modules, mod)
        old = Map.get(manifest.modules, mod)

        dirty? =
          all_dirty? or is_nil(old) or
            source_hash(path) != old.source_hash or
            any_beam_missing?(old, output_dir)

        {mod, dirty?}
      end

    # If this build recompiles any stdlib source, its `@prelude` markers may have
    # changed since the manifest was memoized in a prior same-process build. Evict
    # the memoized manifest ONCE, before the walk, so the build's elaborations see
    # current markers (a single re-scan, not one per module). Sources are stable
    # within a build, so one eviction is sufficient; guarded to skip the cost for
    # the common project build, which never recompiles a stdlib source.
    if recompiles_stdlib_source?(walk, base_dirty, graph.modules),
      do: Program.invalidate_prelude_manifest()

    # Order-independent prediction of "will this module recompile at all this
    # build" — a module is reachable-dirty if IT is base-dirty, or ANY module
    # transitively reachable via `closure_deps` (its full runtime dependency
    # set, not just `order_deps`) is base-dirty. This is what `dep_changed?/2`
    # falls back to for a closure-only dependency the walk hasn't visited yet
    # (only possible across an ambient `@prelude` back-edge): `base_dirty[d]`
    # alone only reflects `d`'s OWN source/beam status and misses `d` being
    # dirtied by a cascade from `d`'s own (already-resolvable) deps — e.g. `d`
    # `use`s `r`, `r`'s source changed, so `d` WILL recompile with a changed
    # interface this build even though `d` itself is untouched and its beam
    # exists. `DepGraph.closure/2` is order-independent (plain graph
    # reachability over `closure_deps_map`, cycle-tolerant), so this is safe
    # to compute up front alongside `base_dirty`. It over-approximates (a
    # reachable-dirty module might still turn out interface-invariant once
    # actually visited) but never under-approximates, matching the "never
    # serve a stale beam" invariant for the one case where the precise
    # interface-hash comparison isn't available yet.
    reachable_dirty =
      for mod <- walk, into: %{} do
        deps = Map.get(closure, mod, [])

        dirty? =
          Map.fetch!(base_dirty, mod) or Enum.any?(DepGraph.closure(closure, deps), &Map.get(base_dirty, &1, false))

        {mod, dirty?}
      end

    state0 = %{
      output_dir: output_dir,
      closure: closure,
      base_dirty: base_dirty,
      reachable_dirty: reachable_dirty,
      module_paths: graph.modules,
      compile_opts:
        opts
        |> Keyword.get(:compile_opts, [])
        |> Keyword.put(:prelude_providers, prelude_providers),
      # `roots` drives BOTH deletion scoping (above) and the standalone
      # interface-hash recomputation below. `Program.module_interface/2` resolves
      # a module's `use`-dependencies through `:cure_source_roots`; without it,
      # any module with a dependency fails to elaborate, its fresh interface hash
      # is `nil`, and every dependent is needlessly treated as changed. Setting
      # the roots here (as `mix cure.compile` does for the compile step) keeps
      # incrementality effective for non-leaf modules.
      roots: roots,
      old: manifest.modules,
      # Seed `new` with the post-deletion kept map, NOT `%{}`. Every module the
      # walk actually visits overwrites its own key below (skip branch: `old`;
      # compile branch: a fresh entry), so this is a no-op for walked modules.
      # For anything NOT in this run's walk — a foreign entry from a build
      # sharing this output_dir (e.g. stdlib vs project), or a source under
      # `source_roots` that simply wasn't passed in `source_paths` this call —
      # it is what carries the entry forward into the saved manifest.
      new: manifest.modules,
      iface: %{},
      compiled: [],
      skipped_fresh: [],
      errors: []
    }

    state = Enum.reduce(walk, state0, &visit_module/2)
    state = Enum.reduce(forced_paths, state, &visit_forced/2)

    summary = %{
      compiled: Enum.sort(state.compiled),
      skipped_fresh: Enum.sort(state.skipped_fresh),
      deleted: Enum.sort(deleted),
      errors: Enum.reverse(state.errors),
      cycles: cycles
    }

    if summary.errors == [] do
      BuildManifest.save(
        %{version: 1, toolchain: toolchain, stdlib_hash: stdlib_hash, modules: state.new},
        output_dir
      )
    end

    {:ok, summary}
  end

  defp visit_module(mod, state) do
    path = Map.fetch!(state.module_paths, mod)
    old = Map.get(state.old, mod)

    dirty? =
      Map.fetch!(state.base_dirty, mod) or
        dep_changed?(Map.get(state.closure, mod, []), state)

    if dirty? do
      compile_and_stage(mod, path, state)
    else
      %{
        state
        | new: Map.put(state.new, mod, old),
          iface: Map.put(state.iface, mod, %{changed: false}),
          skipped_fresh: [mod | state.skipped_fresh]
      }
    end
  end

  defp compile_and_stage(mod, path, state) do
    case Cure.Compiler.compile_file(path, [output_dir: state.output_dir] ++ state.compile_opts) do
      {:ok, _module, _warnings} ->
        # `path` may be a shipped-stdlib source, whose interface the loader
        # memoizes for the lifetime of the OS process (`Program.
        # cached_module_interface/2` — a sound assumption for ordinary
        # compilation, but one this exact recompile just violated). Evict any
        # stale entry before recomputing so a same-process rebuild of a
        # stdlib-recognized path (e.g. two `mix cure.compile_stdlib` runs, or
        # two `compile_dir` calls, sharing a VM) is never compared against a
        # first-run interface that no longer matches the source on disk.
        Program.invalidate_module_interface(path)
        new_hash = interface_hash_for(mod, path, state.roots)

        stored = get_in(state.old, [mod, Access.key(:interface_hash, nil)])
        changed? = is_nil(new_hash) or is_nil(stored) or new_hash != stored

        entry = %{
          source_path: path,
          source_hash: source_hash(path),
          interface_hash: new_hash,
          deps: Map.get(state.closure, mod, []),
          beams: beams_for(mod, state.output_dir, state.module_paths)
        }

        %{
          state
          | new: Map.put(state.new, mod, entry),
            iface: Map.put(state.iface, mod, %{changed: changed?}),
            compiled: [mod | state.compiled]
        }

      {:error, reason} ->
        # not staged; dependents visited later see it as changed (no stored hash)
        %{
          state
          | iface: Map.put(state.iface, mod, %{changed: true}),
            errors: [{mod, reason} | state.errors]
        }
    end
  end

  # Recompute `mod`'s interface hash with `:cure_source_roots` bound so its
  # `use`-dependencies resolve, restoring the prior value afterward (mirrors
  # `Cure.Compiler`'s own `with_source_roots`). Returns nil if the interface
  # cannot be computed, which conservatively marks the module interface-changed.
  defp interface_hash_for(mod, path, roots) do
    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, roots)

    try do
      case Program.module_interface(mod, path) do
        {:ok, iface} -> interface_hash(iface)
        _ -> nil
      end
    after
      if previous == nil,
        do: Process.delete(:cure_source_roots),
        else: Process.put(:cure_source_roots, previous)
    end
  end

  defp visit_forced(path, state) do
    case Cure.Compiler.compile_file(path, [output_dir: state.output_dir] ++ state.compile_opts) do
      {:ok, _module, _warnings} -> state
      {:error, reason} -> %{state | errors: [{path, reason} | state.errors]}
    end
  end

  # True when a base-dirty (source-changed / beam-missing / globally-forced)
  # module in this walk lives under a stdlib source dir — i.e. this build may
  # recompile a stdlib source, whose `@prelude` markers a cached manifest would
  # otherwise still reflect from a prior same-process build.
  defp recompiles_stdlib_source?(walk, base_dirty, module_paths) do
    dirs = Cure.Stdlib.Paths.source_dirs() |> Enum.map(&Path.expand/1)

    dirs != [] and
      Enum.any?(walk, fn mod ->
        Map.fetch!(base_dirty, mod) and
          under_any_dir?(Path.expand(Map.fetch!(module_paths, mod)), dirs)
      end)
  end

  defp under_any_dir?(path, dirs) do
    Enum.any?(dirs, fn dir -> path == dir or String.starts_with?(path, dir <> "/") end)
  end

  # A module is stale if any of its closure deps changed. For a dep already
  # visited this walk, "changed" means its interface hash moved (the precise
  # interface-level cascade). A dep NOT yet visited can only be an ambient
  # `@prelude` cycle back-edge — the acyclic `order_deps` walk places every real
  # use-dep first — so we fall back to `reachable_dirty[d]`: whether `d` (or
  # anything `d` transitively depends on via the closure graph) will recompile
  # at all this build. `base_dirty[d]` alone is NOT enough here — it only
  # reflects `d`'s own source/beam status, missing the case where `d` will be
  # dirtied this same build by a cascade from `d`'s own dependencies (e.g. `d`
  # `use`s `r`, `r`'s source changed — `d`'s interface WILL change, but `d`
  # itself is untouched and its beam still exists). `reachable_dirty` closes
  # that gap; see its derivation in `run/4` for why it's sound and
  # order-independent.
  defp dep_changed?(deps, state) do
    Enum.any?(deps, fn d ->
      case Map.get(state.iface, d) do
        %{changed: changed?} -> changed?
        nil -> Map.get(state.reachable_dirty, d, false)
      end
    end)
  end

  defp delete_removed(manifest, roots, output_dir) do
    {removed, kept} =
      Enum.split_with(manifest.modules, fn {_mod, entry} ->
        under_roots?(entry.source_path, roots) and not File.exists?(entry.source_path)
      end)

    Enum.each(removed, fn {_mod, entry} ->
      Enum.each(entry.beams, fn b -> File.rm(Path.join(output_dir, b)) end)
    end)

    {%{manifest | modules: Map.new(kept)}, Enum.map(removed, fn {mod, _} -> mod end)}
  end

  defp under_roots?(path, roots) do
    abs = Path.expand(path)
    Enum.any?(roots, fn r -> abs == r or String.starts_with?(abs, r <> "/") end)
  end

  defp source_hash(path), do: :crypto.hash(:sha256, File.read!(path))

  defp any_beam_missing?(%{beams: beams}, output_dir) do
    Enum.any?(beams, fn b -> not File.exists?(Path.join(output_dir, b)) end)
  end

  # `known_modules` is `graph.modules` (`state.module_paths`) — every top-level
  # module name scanned this run. A `Cure.<mod>.*.beam` wildcard match is only a
  # genuine lifted submodule of `mod` if its stripped name is NOT itself one of
  # these; Cure's dotted naming convention means an independently-declared
  # sibling (e.g. real stdlib modules `Std.Otp` / `Std.Otp.Call`) can otherwise
  # false-positive-match and later get deleted alongside `mod`'s own beam.
  defp beams_for(mod, output_dir, known_modules) do
    prefix = "Cure." <> mod

    exact = Path.wildcard(Path.join(output_dir, prefix <> ".beam"))

    lifted =
      Path.join(output_dir, prefix <> ".*.beam")
      |> Path.wildcard()
      |> Enum.reject(fn beam_path ->
        candidate = beam_path |> Path.basename(".beam") |> String.trim_leading("Cure.")
        Map.has_key?(known_modules, candidate)
      end)

    (exact ++ lifted)
    |> Enum.map(&Path.basename/1)
    |> Enum.uniq()
    |> Enum.sort()
  end
end
