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
  @spec interface_hash(map()) :: binary()
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

  @doc "SHA-256 over `Cure.Std.*.beam` content in `output_dir`, sorted. External stdlib fingerprint for project builds."
  @spec stdlib_fingerprint(String.t()) :: binary()
  def stdlib_fingerprint(output_dir) do
    output_dir
    |> Path.join("Cure.Std.*.beam")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.reduce(:crypto.hash_init(:sha256), fn f, acc ->
      :crypto.hash_update(acc, File.read!(f))
    end)
    |> :crypto.hash_final()
  end

  defp run(graph, source_paths, output_dir, opts) do
    {:ok, _ordered, cycles} = DepGraph.order(graph)
    closure = DepGraph.closure_deps_map(graph)
    walk = DepGraph.toposort(closure, Map.keys(closure))

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

    state0 = %{
      output_dir: output_dir,
      closure: closure,
      module_paths: graph.modules,
      compile_opts: Keyword.get(opts, :compile_opts, []),
      # `roots` drives BOTH deletion scoping (above) and the standalone
      # interface-hash recomputation below. `Program.module_interface/2` resolves
      # a module's `use`-dependencies through `:cure_source_roots`; without it,
      # any module with a dependency fails to elaborate, its fresh interface hash
      # is `nil`, and every dependent is needlessly treated as changed. Setting
      # the roots here (as `mix cure.compile` does for the compile step) keeps
      # incrementality effective for non-leaf modules.
      roots: roots,
      all_dirty?: all_dirty?,
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
      state.all_dirty? or is_nil(old) or
        source_hash(path) != old.source_hash or
        any_beam_missing?(old, state.output_dir) or
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
        {:ok, iface} -> interface_hash(iface.export_env)
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

  defp dep_changed?(deps, state) do
    Enum.any?(deps, fn d ->
      match?(%{changed: true}, Map.get(state.iface, d))
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
