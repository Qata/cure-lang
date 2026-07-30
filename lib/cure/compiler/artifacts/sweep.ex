defmodule Cure.Compiler.Artifacts.Sweep do
  @moduledoc "The single discovery, verification, repair, and publication sweep."

  alias Cure.Compiler.Artifacts
  alias Cure.Compiler.Artifacts.Result
  alias Cure.Compiler.BuildManifest

  @spec run(keyword()) :: {:ok, Result.t()} | {:error, term()}
  def run(opts) do
    output_dir = Keyword.fetch!(opts, :output_dir)

    if Keyword.get(opts, :repair, true) do
      repair(opts, output_dir)
    else
      Artifacts.with_cache(fn -> validate(output_dir, opts) end)
    end
  end

  defp repair(opts, output_dir) do
    source_roots = opts |> Keyword.fetch!(:source_roots) |> List.wrap()

    source_paths =
      case Keyword.get(opts, :source_paths) do
        nil ->
          source_roots
          |> Enum.flat_map(&Path.wildcard(Path.join(&1, "**/*.cure")))
          |> Enum.uniq()
          |> Enum.sort()

        paths ->
          paths |> List.wrap() |> Enum.map(&Path.expand/1) |> Enum.uniq() |> Enum.sort()
      end

    incremental_opts =
      opts
      |> Keyword.take([
        :force,
        :stdlib_artifact_digest,
        :verify_stdlib,
        :package_artifact_digests,
        :package_artifact_sets,
        :compile_opts
      ])
      |> Keyword.put(:source_roots, source_roots)
      |> Keyword.put(:artifact_kind, Keyword.get(opts, :kind, :project))

    with {:ok, summary} <-
           Cure.Compiler.Incremental.compile_dir(
             source_paths,
             output_dir,
             incremental_opts
           ),
         [] <- summary.errors,
         {:ok, manifest} <- Artifacts.open_verified_set(output_dir, verification: :cached) do
      {:ok, result(manifest, summary)}
    else
      {:ok, %{errors: errors}} -> {:error, {:artifact_sweep_failed, errors}}
      errors when is_list(errors) -> {:error, {:artifact_sweep_failed, errors}}
      {:error, _} = error -> error
    end
  end

  defp validate(output_dir, opts) do
    expected_kind = Keyword.get(opts, :kind)

    verification = Keyword.get(opts, :verification, :cached)

    with {:ok, manifest} <- Artifacts.open_verified_set(output_dir, verification: verification),
         true <- is_nil(expected_kind) or manifest.kind == expected_kind do
      stats = Artifacts.hash_stats()

      {:ok,
       %Result{
         workspace_key: manifest.workspace_key,
         input_snapshot: manifest.input_snapshot,
         artifact_digest: manifest.artifact_digest,
         artifact_root: manifest.artifact_root,
         reused: manifest.modules |> Map.keys() |> Enum.sort(),
         verification: verification,
         hashes_computed: stats.computed,
         hashes_reused: stats.reused,
         manifest_path: Path.join(manifest.artifact_root, BuildManifest.filename())
       }}
    else
      false -> {:error, :artifact_kind_mismatch}
      {:error, _} = error -> error
    end
  end

  defp result(manifest, summary) do
    stats = Map.get(summary, :hash_stats, %{computed: 0, reused: 0})

    %Result{
      workspace_key: manifest.workspace_key,
      input_snapshot: manifest.input_snapshot,
      artifact_digest: manifest.artifact_digest,
      artifact_root: manifest.artifact_root,
      reused: summary.skipped_fresh,
      rebuilt: summary.rebuild_reasons,
      removed: Map.new(summary.deleted, &{&1, :orphan}),
      errors: summary.errors,
      warnings: summary.warnings,
      cycles: summary.cycles,
      verification: :full,
      hashes_computed: stats.computed,
      hashes_reused: stats.reused,
      manifest_path: Path.join(manifest.artifact_root, BuildManifest.filename())
    }
  end
end
