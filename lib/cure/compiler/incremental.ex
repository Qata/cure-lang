defmodule Cure.Compiler.Incremental do
  @moduledoc """
  Interface-level incremental driver for multi-file Cure builds.

  Recompiles a module only when its source content changed, one of its output
  beams is missing, a direct dependency's interface changed, or the compiler
  itself changed. See `docs/superpowers/specs/2026-07-18-incremental-compilation-design.md`.
  """

  alias Cure.Compiler.{Artifacts, BuildManifest, DepGraph}
  alias Cure.Compiler.Artifacts.{Lock, Writer}
  alias Cure.Elab.Program

  @type summary :: %{
          compiled: [String.t()],
          skipped_fresh: [String.t()],
          deleted: [String.t()],
          errors: [{term(), term()}],
          warnings: %{optional(String.t()) => list()},
          cycles: [list()],
          rebuild_reasons: %{optional(String.t()) => [atom()]}
        }

  @doc """
  SHA-256 of a module's own public semantic interface. Dependency hashes are
  tracked separately as validation metadata; recursively including them here
  would make cyclic interface graphs unable to reach a cryptographic fixed
  point.
  """
  @spec interface_hash(Cure.Compiler.ModuleInterface.t() | map()) :: binary()
  def interface_hash(%Cure.Compiler.ModuleInterface{interface_hash: hash}), do: hash

  def interface_hash(export_env) do
    :crypto.hash(:sha256, :erlang.term_to_binary(export_env, [:deterministic]))
  end

  @spec compile_dir([Path.t()], String.t(), keyword()) :: {:ok, summary()} | {:error, term()}
  def compile_dir(source_paths, output_dir, opts \\ []) do
    source_paths = source_paths |> Enum.map(&Path.expand/1) |> Enum.uniq() |> Enum.sort()
    File.mkdir_p!(output_dir)

    with :ok <- verify_dependency_sets(opts),
         {:ok, known_modules} <- dependency_module_names(opts),
         scan_result <-
           DepGraph.scan(source_paths,
             validate_dependencies: true,
             known_modules: known_modules
           ) do
      case scan_result do
        {:error, reason} ->
          {:error, reason}

        {:ok, graph} ->
          Writer.transact(output_dir, fn stage ->
            Artifacts.with_cache(fn ->
              case run(graph, source_paths, stage, opts) do
                {:ok, %{errors: []} = summary} ->
                  {:ok, Map.put(summary, :hash_stats, Artifacts.hash_stats())}

                {:ok, summary} ->
                  {:no_publish, Map.put(summary, :hash_stats, Artifacts.hash_stats())}
              end
            end)
          end)
      end
    end
  end

  defp dependency_module_names(opts) do
    package_roots =
      opts
      |> Keyword.get(:package_artifact_sets, %{})
      |> Map.values()
      |> Enum.map(&Map.fetch!(&1, :root))

    with {:ok, package_modules} <- module_names_from_roots(package_roots),
         {:ok, stdlib_modules} <- stdlib_module_names(opts) do
      {:ok, package_modules |> MapSet.union(stdlib_modules) |> MapSet.to_list()}
    end
  end

  defp module_names_from_roots(roots) do
    Enum.reduce_while(roots, {:ok, MapSet.new()}, fn root, {:ok, modules} ->
      case Artifacts.open_verified_set(root) do
        {:ok, set} ->
          {:cont, {:ok, MapSet.union(modules, MapSet.new(Map.keys(set.modules)))}}

        {:error, reason} ->
          {:halt, {:error, {:dependency_artifact_set_invalid, root, reason}}}
      end
    end)
  end

  defp stdlib_module_names(opts) do
    if Keyword.get(opts, :verify_stdlib, false) do
      case Artifacts.open_verified_set(
             kind: :stdlib,
             candidates: Cure.Stdlib.Paths.beam_dirs()
           ) do
        {:ok, set} -> {:ok, MapSet.new(Map.keys(set.modules))}
        {:error, reason} -> {:error, {:dependency_artifact_set_invalid, :stdlib, reason}}
      end
    else
      {:ok, MapSet.new()}
    end
  end

  defp verify_dependency_sets(opts) do
    with :ok <- verify_stdlib_set(opts) do
      opts
      |> Keyword.get(:package_artifact_sets, %{})
      |> Enum.reduce_while(:ok, fn {package, dependency}, :ok ->
        root = Map.fetch!(dependency, :root)
        expected = Map.get(dependency, :artifact_digest)

        case Artifacts.open_verified_set(root) do
          {:ok, %{artifact_digest: artifact_digest}}
          when is_nil(expected) or artifact_digest == expected ->
            {:cont, :ok}

          {:ok, %{artifact_digest: artifact_digest}} ->
            {:halt, {:error, {:dependency_artifact_digest_mismatch, {:package, package}, expected, artifact_digest}}}

          {:error, reason} ->
            {:halt, {:error, {:dependency_artifact_set_invalid, {:package, package}, reason}}}
        end
      end)
    end
  end

  defp verify_stdlib_set(opts) do
    if Keyword.get(opts, :verify_stdlib, false) do
      expected = Keyword.get(opts, :stdlib_artifact_digest)

      case Artifacts.open_verified_set(
             kind: :stdlib,
             candidates: Cure.Stdlib.Paths.beam_dirs()
           ) do
        {:ok, %{artifact_digest: artifact_digest}}
        when is_nil(expected) or artifact_digest == expected ->
          :ok

        {:ok, %{artifact_digest: artifact_digest}} ->
          {:error, {:dependency_artifact_digest_mismatch, :stdlib, expected, artifact_digest}}

        {:error, reason} ->
          {:error, {:dependency_artifact_set_invalid, :stdlib, reason}}
      end
    else
      :ok
    end
  end

  @doc """
  Generation of the first complete verified stdlib candidate a project build
  will actually link against. Candidate order comes from
  `Cure.Stdlib.Paths.beam_dirs/0`, but invalid earlier directories are rejected
  as whole sets rather than becoming a filename-based fingerprint.

  This is the fingerprint a project build stores and re-checks to decide whether
  the stdlib changed under it. Resolving the real beam dir (instead of the
  project's `output_dir`, which for a non-default `--output-dir` holds no stdlib
  beams) is what lets a project built to an unusual output dir still notice a
  stdlib change and rebuild. Returns a stable empty-set hash when no verified
  stdlib generation exists yet, so the first real stdlib compile moves it.
  """
  @spec stdlib_fingerprint() :: binary()
  def stdlib_fingerprint do
    case Artifacts.open_verified_set(
           kind: :stdlib,
           candidates: Cure.Stdlib.Paths.beam_dirs()
         ) do
      {:ok, %{artifact_digest: artifact_digest}} -> artifact_digest
      {:error, _reason} -> stdlib_fingerprint_over([])
    end
  end

  @doc """
  SHA-256 over `Cure.Std.*.beam` content in a specific `dir`, sorted. Prefer the
  zero-arity `stdlib_fingerprint/0`, which resolves the stdlib's real beam
  location; this arity is for pointing at an explicit directory (tests, tools).
  """
  @spec stdlib_fingerprint(String.t()) :: binary()
  def stdlib_fingerprint(dir) do
    case Artifacts.open_verified_set(dir) do
      {:ok, %{kind: :stdlib, artifact_digest: artifact_digest}} -> artifact_digest
      _ -> stdlib_fingerprint_over([])
    end
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

  Ordering follows the explicit `use` graph. Among modules whose explicit
  dependencies are already satisfied, ambient prelude providers are selected
  first. This gives new providers a BEAM before ordinary implicit consumers
  without adding synthetic edges or manufacturing prelude cycles. Qualified-call
  closure edges remain order-free. Change propagation still uses the conservative
  closure superset — see `dep_changed?/2`.
  """
  @spec compile_order(DepGraph.t()) :: [String.t()]
  def compile_order(graph) do
    order = DepGraph.order_deps_map(graph)
    DepGraph.toposort(order, Map.keys(order), DepGraph.prelude_provider_names(graph))
  end

  defp run(graph, source_paths, output_dir, opts) do
    {:ok, _ordered, cycles} = DepGraph.order(graph)
    closure = DepGraph.closure_deps_map(graph)
    compile_dependencies = DepGraph.order_deps_map(graph)

    components =
      DepGraph.components(
        compile_dependencies,
        Map.keys(graph.modules),
        DepGraph.prelude_provider_names(graph)
      )

    walk = List.flatten(components)
    prelude_providers = DepGraph.prelude_provider_names(graph)

    forced_paths =
      for {path, node} <- graph.nodes,
          not node.blank?,
          not is_binary(node.module),
          do: path

    force? =
      Keyword.get(opts, :force, false) or
        System.get_env("CURE_FULL_REBUILD") not in [nil, ""]

    compiler_hash = BuildManifest.toolchain_fingerprint()
    current_context = build_context(compiler_hash, opts)
    workspace_key = workspace_key(current_context)

    {manifest, manifest_reason} =
      if force? do
        {BuildManifest.empty(workspace_key), nil}
      else
        case BuildManifest.read(output_dir) do
          {:ok, manifest} -> {manifest, nil}
          {:error, reason} -> {BuildManifest.empty(""), reason}
        end
      end

    source_records =
      Map.new(source_paths, fn path ->
        module_name = Enum.find_value(graph.modules, fn {name, module_path} -> if module_path == path, do: name end)
        expected = module_name && get_in(manifest, [:modules, module_name, :source])
        {path, Artifacts.record_source(path, expected, manifest.validated_at)}
      end)

    input_snapshot = input_snapshot(compiler_hash, source_records, opts)
    :ok = Lock.set_intended_generation(input_snapshot)

    stdlib_artifact_digest =
      Keyword.get(opts, :stdlib_artifact_digest, get_in(manifest, [:dependencies, :stdlib]))

    package_artifact_digests = Keyword.get(opts, :package_artifact_digests, %{})
    old_package_artifact_digests = get_in(manifest, [:dependencies, :packages]) || %{}
    context_mismatch? = manifest.context != current_context

    all_dirty? =
      force? or manifest.workspace_key != workspace_key or context_mismatch? or
        (Keyword.has_key?(opts, :stdlib_artifact_digest) and
           get_in(manifest, [:dependencies, :stdlib]) != stdlib_artifact_digest) or
        old_package_artifact_digests != package_artifact_digests

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
    {base_dirty, rebuild_reasons} =
      Enum.reduce(walk, {%{}, %{}}, fn mod, {dirty_acc, reason_acc} ->
        path = Map.fetch!(graph.modules, mod)
        old = Map.get(manifest.modules, mod)

        reasons =
          []
          |> maybe_reason(force?, :forced)
          |> maybe_reason(not is_nil(manifest_reason), manifest_reason)
          |> maybe_reason(manifest.workspace_key != workspace_key, :compiler_context_mismatch)
          |> maybe_reason(context_mismatch?, :compiler_context_mismatch)
          |> maybe_reason(
            Keyword.has_key?(opts, :stdlib_artifact_digest) and
              get_in(manifest, [:dependencies, :stdlib]) != stdlib_artifact_digest,
            :dependency_artifact_digest_mismatch
          )
          |> maybe_reason(
            old_package_artifact_digests != package_artifact_digests,
            :dependency_artifact_digest_mismatch
          )
          |> maybe_reason(is_nil(old), :new_module)
          |> maybe_reason(
            not is_nil(old) and
              get_in(source_records, [path, :sha256]) != get_in(old, [:source, :sha256]),
            :source_hash_mismatch
          )
          |> then(fn reasons ->
            if old,
              do:
                Enum.uniq(
                  reasons ++
                    Artifacts.verify_entry(old, output_dir,
                      verification: :cached,
                      validated_at: manifest.validated_at
                    )
                ),
              else: reasons
          end)

        {
          Map.put(dirty_acc, mod, all_dirty? or reasons != []),
          if(reasons == [], do: reason_acc, else: Map.put(reason_acc, mod, reasons))
        }
      end)

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
    state0 = %{
      output_dir: output_dir,
      closure: closure,
      compile_dependencies: compile_dependencies,
      base_dirty: base_dirty,
      module_paths: graph.modules,
      source_records: source_records,
      compile_opts:
        opts
        |> Keyword.get(:compile_opts, [])
        |> Keyword.put(:prelude_providers, prelude_providers)
        |> Keyword.put(:module_index, graph.module_index)
        |> Keyword.put(:artifact_provenance, %{
          compiler_hash: compiler_hash,
          producer_snapshot: input_snapshot
        }),
      old: manifest.modules,
      current_hashes: Map.new(manifest.modules, fn {name, entry} -> {name, entry.interface_hash} end),
      revisions: Map.new(walk, &{&1, 0}),
      seen_dependency_revisions: %{},
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
      errors: [],
      warnings: %{},
      rebuild_reasons: rebuild_reasons,
      progress: Keyword.get(opts, :progress),
      migration_diagnostic_sink: Keyword.get(opts, :migration_diagnostic_sink)
    }

    state = Enum.reduce(components, state0, &visit_component/2)
    state = stabilize_interface_edges(walk, state)
    state = Enum.reduce(forced_paths, state, &visit_forced/2)

    warnings =
      Map.new(state.new, fn {module, entry} ->
        count = Map.get(entry, :warning_count, 0)
        {module, if(count > 0, do: Map.get(state.warnings, module, [{:persisted_warning_count, count}]), else: [])}
      end)
      |> Map.reject(fn {_module, warnings} -> warnings == [] end)

    summary = %{
      compiled: Enum.sort(state.compiled),
      skipped_fresh: Enum.sort(state.skipped_fresh),
      deleted: Enum.sort(deleted),
      errors: Enum.reverse(state.errors),
      warnings: warnings,
      cycles: cycles,
      rebuild_reasons: state.rebuild_reasons
    }

    publish_manifest(
      summary,
      state,
      workspace_key,
      input_snapshot,
      compiler_hash,
      stdlib_artifact_digest,
      package_artifact_digests,
      output_dir,
      opts
    )
  end

  defp publish_manifest(
         summary,
         state,
         workspace_key,
         input_snapshot,
         compiler_hash,
         stdlib_artifact_digest,
         package_artifact_digests,
         output_dir,
         opts
       ) do
    if summary.errors == [] do
      validated_at = Artifacts.filesystem_timestamp(output_dir)

      candidate =
        BuildManifest.seal(%{
          version: 3,
          kind: Keyword.get(opts, :artifact_kind, :project),
          workspace_key: workspace_key,
          input_snapshot: input_snapshot,
          artifact_digest: nil,
          validated_at: validated_at,
          context: build_context(compiler_hash, opts),
          dependencies: %{
            stdlib: stdlib_artifact_digest,
            packages: package_artifact_digests
          },
          modules: state.new,
          expected_modules: state.new |> Map.keys() |> Enum.sort()
        })

      {candidate, removed_orphans} = remove_orphans(candidate, output_dir)
      summary = %{summary | deleted: Enum.sort(Enum.uniq(summary.deleted ++ removed_orphans))}

      artifact_paths =
        candidate.modules
        |> Map.values()
        |> Enum.flat_map(&Map.get(&1, :beams, []))

      # Candidate publication is a fresh read boundary. Classification and
      # compilation may have cached earlier metadata, but the final verifier
      # must hash the exact bytes that are about to become current.
      Artifacts.invalidate_paths(artifact_paths, output_dir)

      case Artifacts.verify_manifest(candidate, output_dir, verification: :full) do
        :ok ->
          BuildManifest.save(candidate, output_dir)
          {:ok, summary}

        {:error, details} ->
          {:ok,
           %{
             summary
             | errors: [
                 {:artifact_set, {:artifact_error, "Artifact-set verification failed", details}}
               ]
           }}
      end
    else
      {:ok, summary}
    end
  end

  defp build_context(toolchain, opts) do
    %{
      compiler_hash: toolchain,
      language_edition: Cure.Edition.current(),
      otp_release: to_string(:erlang.system_info(:otp_release)),
      elixir_version: System.version(),
      target: :beam,
      source_roots_hash:
        opts
        |> Keyword.get(:source_roots, [])
        |> Enum.map(&Path.expand/1)
        |> Enum.sort()
        |> :erlang.term_to_binary([:deterministic])
        |> then(&:crypto.hash(:sha256, &1)),
      codegen_options_hash:
        opts
        |> Keyword.get(:compile_opts, [])
        |> normalize_options()
        |> :erlang.term_to_binary([:deterministic])
        |> then(&:crypto.hash(:sha256, &1))
    }
  end

  defp workspace_key(context),
    do: :crypto.hash(:sha256, :erlang.term_to_binary(context, [:deterministic]))

  defp input_snapshot(compiler_hash, source_records, opts) do
    sources =
      source_records
      |> Enum.map(fn {path, record} -> {Path.expand(path), record.sha256} end)
      |> Enum.sort()

    payload = %{
      compiler_hash: compiler_hash,
      sources: sources,
      edition: Cure.Edition.current(),
      otp_release: to_string(:erlang.system_info(:otp_release)),
      target: :beam,
      compile_options: opts |> Keyword.get(:compile_opts, []) |> normalize_options(),
      stdlib: Keyword.get(opts, :stdlib_artifact_digest),
      packages: Keyword.get(opts, :package_artifact_digests, %{})
    }

    :crypto.hash(:sha256, :erlang.term_to_binary(payload, [:deterministic]))
  end

  defp normalize_options(options) when is_list(options) do
    if Keyword.keyword?(options) do
      options
      |> Enum.map(fn {key, value} -> {key, normalize_options(value)} end)
      |> Enum.sort()
    else
      Enum.map(options, &normalize_options/1)
    end
  end

  defp normalize_options(%MapSet{} = set) do
    set
    |> MapSet.to_list()
    |> Enum.map(&normalize_options/1)
    |> Enum.sort()
  end

  defp normalize_options(%module{} = struct) do
    {module, struct |> Map.from_struct() |> normalize_options()}
  end

  defp normalize_options(options) when is_map(options) do
    options
    |> Map.to_list()
    |> Enum.map(fn {key, value} -> {key, normalize_options(value)} end)
    |> Enum.sort()
  end

  defp normalize_options(value), do: value

  defp remove_orphans(manifest, output_dir) do
    claimed =
      manifest.modules
      |> Map.values()
      |> Enum.flat_map(&Map.get(&1, :artifacts, []))
      |> Enum.map(&Map.fetch!(&1, :path))
      |> MapSet.new()

    orphans =
      output_dir
      |> Path.join("*.beam")
      |> Path.wildcard()
      |> Enum.reject(&(Path.basename(&1) in claimed))

    removed =
      Enum.flat_map(orphans, fn path ->
        case File.rm(path) do
          :ok -> [Path.basename(path)]
          {:error, _reason} -> []
        end
      end)

    {manifest, removed}
  end

  defp visit_module(mod, state) do
    path = Map.fetch!(state.module_paths, mod)
    old = Map.get(state.old, mod)

    changed_dependencies =
      changed_dependencies(mod, Map.get(state.closure, mod, []), state)

    dirty? =
      Map.fetch!(state.base_dirty, mod) or
        changed_dependencies != []

    result =
      if dirty? do
        state =
          if changed_dependencies == [] do
            state
          else
            update_in(state.rebuild_reasons, fn reasons ->
              Map.update(
                reasons,
                mod,
                [:dependency_interface_changed],
                &Enum.uniq([:dependency_interface_changed | &1])
              )
            end)
          end

        compile_and_stage(mod, path, state)
      else
        case Artifacts.load_recorded_artifacts(Map.get(old, :artifacts, []), state.output_dir) do
          :ok ->
            refreshed =
              old
              |> Map.put(:source, Map.fetch!(state.source_records, path))
              |> Map.put(:artifacts, refresh_artifact_stats(old.artifacts, state.output_dir))

            %{
              state
              | new: Map.put(state.new, mod, refreshed),
                iface: Map.put(state.iface, mod, %{changed: false}),
                skipped_fresh: [mod | state.skipped_fresh]
            }

          {:error, reason} ->
            %{
              state
              | iface: Map.put(state.iface, mod, %{changed: true}),
                errors: [{mod, {:artifact_load_failed, reason}} | state.errors]
            }
        end
      end

    remember_dependency_revisions(mod, result)
  end

  defp visit_component([mod], state), do: visit_module(mod, state)

  defp visit_component(members, state) do
    member_set = MapSet.new(members)

    external_dependencies =
      members
      |> Enum.flat_map(&Map.get(state.closure, &1, []))
      |> Enum.reject(&MapSet.member?(member_set, &1))
      |> Enum.uniq()

    dirty? =
      Enum.any?(members, &Map.fetch!(state.base_dirty, &1)) or
        Enum.any?(members, fn member ->
          changed_dependencies(member, external_dependencies, state) != []
        end)

    if dirty? do
      base_dirty = Enum.reduce(members, state.base_dirty, &Map.put(&2, &1, true))

      rebuild_reasons =
        Enum.reduce(members, state.rebuild_reasons, fn member, reasons ->
          Map.update(reasons, member, [:dependency_cycle_invalidated], fn existing ->
            Enum.uniq([:dependency_cycle_invalidated | existing])
          end)
        end)

      Enum.reduce(
        members,
        %{state | base_dirty: base_dirty, rebuild_reasons: rebuild_reasons},
        &visit_module/2
      )
    else
      Enum.reduce(members, state, &visit_module/2)
    end
  end

  defp compile_and_stage(mod, path, state) do
    notify_progress(state, {:compile_started, mod, path})

    compile_opts =
      maybe_put_migration_sink(state.compile_opts, state.migration_diagnostic_sink)

    case Cure.Compiler.compile_file_with_artifact(
           path,
           [output_dir: state.output_dir] ++ compile_opts
         ) do
      {:ok, _module, warnings, artifact} ->
        {new_hash, dependency_hashes} =
          case artifact do
            %Cure.Elab.CheckedModule{
              module_name: ^mod,
              interface: %Cure.Compiler.ModuleInterface{} = interface
            } ->
              {interface_hash(interface), interface.dependency_interface_hashes}

            _ ->
              {nil, %{}}
          end

        previous_hash = Map.get(state.current_hashes, mod)

        previous_dependency_hashes =
          state.old
          |> Map.get(mod, %{})
          |> Map.get(:dependency_interface_hashes)

        changed_now? =
          is_nil(new_hash) or is_nil(previous_hash) or new_hash != previous_hash or
            is_nil(previous_dependency_hashes) or dependency_hashes != previous_dependency_hashes

        # A revision is a build-local "semantic context changed" bit, not a
        # compile counter. A module may be revisited while closing an interface
        # cycle; recompiling it again must not manufacture a fresh revision and
        # circulate invalidation forever.
        revision = max(Map.get(state.revisions, mod, 0), if(changed_now?, do: 1, else: 0))

        beams = beams_for(mod, state.output_dir, state.module_paths)
        Artifacts.invalidate_paths(beams, state.output_dir)

        with {:ok, artifacts} <- Artifacts.record_paths(beams, state.output_dir),
             :ok <- Artifacts.load_recorded_artifacts(artifacts, state.output_dir) do
          entry = %{
            source: Map.fetch!(state.source_records, path),
            warning_count: length(warnings),
            interface_hash: new_hash,
            dependency_interface_hashes: dependency_hashes,
            edges: %{
              compile_order: Map.get(state.compile_dependencies, mod, []),
              interface: Map.get(state.closure, mod, []),
              runtime: Map.get(state.closure, mod, [])
            },
            artifacts: artifacts
          }

          %{
            state
            | new: Map.put(state.new, mod, entry),
              iface: Map.put(state.iface, mod, %{changed: changed_now?}),
              current_hashes: Map.put(state.current_hashes, mod, new_hash),
              revisions: Map.put(state.revisions, mod, revision),
              warnings: if(warnings == [], do: state.warnings, else: Map.put(state.warnings, mod, warnings)),
              compiled: Enum.uniq([mod | state.compiled]),
              skipped_fresh: List.delete(state.skipped_fresh, mod)
          }
        else
          {:error, reason} ->
            %{
              state
              | iface: Map.put(state.iface, mod, %{changed: true}),
                revisions: Map.put(state.revisions, mod, 1),
                errors: [{mod, {:artifact_record_failed, reason}} | state.errors]
            }
        end

      {:error, reason} ->
        # not staged; dependents visited later see it as changed (no stored hash)
        %{
          state
          | iface: Map.put(state.iface, mod, %{changed: true}),
            revisions: Map.put(state.revisions, mod, 1),
            errors: [{mod, reason} | state.errors]
        }
    end
  end

  defp notify_progress(%{progress: progress}, event) when is_function(progress, 1) do
    progress.(event)
    :ok
  rescue
    _ -> :ok
  catch
    _, _ -> :ok
  end

  defp notify_progress(_state, _event), do: :ok

  defp maybe_put_migration_sink(opts, sink) when is_function(sink, 2),
    do: Keyword.put(opts, :migration_diagnostic_sink, sink)

  defp maybe_put_migration_sink(opts, _sink), do: opts

  defp visit_forced(path, state) do
    compile_opts = maybe_put_migration_sink(state.compile_opts, state.migration_diagnostic_sink)

    case Cure.Compiler.compile_file(path, [output_dir: state.output_dir] ++ compile_opts) do
      {:ok, _module, []} -> state
      {:ok, _module, warnings} -> %{state | warnings: Map.put(state.warnings, path, warnings)}
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

  # A consumer is stale when a dependency has advanced beyond the revision the
  # consumer last observed. Compile-order SCCs are visited dependency-first;
  # interface-only cycles and back-edges converge in
  # `stabilize_interface_edges/2`.
  defp changed_dependencies(mod, deps, state) do
    seen = Map.get(state.seen_dependency_revisions, mod, %{})

    Enum.filter(deps, fn d ->
      Map.get(state.revisions, d, 0) > Map.get(seen, d, 0) and
        not dependency_observation_current?(mod, d, state)
    end)
  end

  # A module compiled before an order-free qualified dependency may already
  # have loaded that dependency's canonical interface through Program's module
  # loader. Once the dependency is visited, compare semantic hashes before
  # scheduling a stabilization pass. Matching hashes prove the consumer was
  # checked against exactly the interface now emitted, so recompiling it would
  # be pure duplicate work.
  defp dependency_observation_current?(mod, dependency, state) do
    with true <- dependency in state.compiled,
         %{dependency_interface_hashes: observed} <- Map.get(state.new, mod),
         observed_hash when is_binary(observed_hash) <- Map.get(observed, dependency),
         current_hash when is_binary(current_hash) <- Map.get(state.current_hashes, dependency) do
      observed_hash == current_hash
    else
      _ -> false
    end
  end

  defp remember_dependency_revisions(mod, state) do
    revisions =
      state.closure
      |> Map.get(mod, [])
      |> Map.new(&{&1, Map.get(state.revisions, &1, 0)})

    %{state | seen_dependency_revisions: Map.put(state.seen_dependency_revisions, mod, revisions)}
  end

  defp stabilize_interface_edges(walk, state) do
    pending =
      Enum.filter(walk, fn mod ->
        changed_dependencies(mod, Map.get(state.closure, mod, []), state) != []
      end)

    if pending == [] or state.errors != [] do
      state
    else
      base_dirty = Enum.reduce(pending, state.base_dirty, &Map.put(&2, &1, true))
      pending_set = MapSet.new(pending)

      state =
        Enum.reduce(walk, %{state | base_dirty: base_dirty}, fn mod, acc ->
          if MapSet.member?(pending_set, mod), do: visit_module(mod, acc), else: acc
        end)

      stabilize_interface_edges(walk, state)
    end
  end

  defp delete_removed(manifest, roots, output_dir) do
    {removed, kept} =
      Enum.split_with(manifest.modules, fn {_mod, entry} ->
        source_path = get_in(entry, [:source, :path])
        is_binary(source_path) and under_roots?(source_path, roots) and not File.exists?(source_path)
      end)

    Enum.each(removed, fn {_mod, entry} ->
      Enum.each(entry.artifacts, fn artifact -> File.rm(Path.join(output_dir, artifact.path)) end)
    end)

    {%{manifest | modules: Map.new(kept)}, Enum.map(removed, fn {mod, _} -> mod end)}
  end

  defp under_roots?(path, roots) do
    abs = Path.expand(path)
    Enum.any?(roots, fn r -> abs == r or String.starts_with?(abs, r <> "/") end)
  end

  defp refresh_artifact_stats(artifacts, root) do
    Enum.map(artifacts, fn artifact ->
      path = Path.join(root, artifact.path)

      case File.stat(path, time: :posix) do
        {:ok, stat} ->
          signature = Artifacts.stat_signature(stat)

          if signature == artifact.stat do
            artifact
          else
            {:ok, refreshed} = Artifacts.record(artifact.path, root)
            refreshed
          end

        {:error, _reason} ->
          artifact
      end
    end)
  end

  defp maybe_reason(reasons, true, reason), do: [reason | reasons]
  defp maybe_reason(reasons, false, _reason), do: reasons

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
