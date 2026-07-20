defmodule Cure.Diagnostic.Host do
  @moduledoc "Single presentation boundary for compiler and host command output."

  alias Cure.Diagnostic.{Operational, Sink}

  @doc "Render a compiler or host failure with its authored source context."
  @spec render(term(), String.t(), String.t() | nil) :: String.t()
  def render(reason, file, source \\ nil) when is_binary(file) do
    source = source || read_source(file)

    case convert(reason, file, source) do
      {:ok, diagnostic, registry} ->
        Sink.new(format: :plain, registry: registry)
        |> Sink.render(diagnostic)
    end
  end

  @doc "Render an already-structured diagnostic through the shared sink."
  @spec render_diagnostic(Cure.Diagnostic.t(), keyword()) :: String.t()
  def render_diagnostic(%Cure.Diagnostic{} = diagnostic, opts \\ []) do
    Sink.new(
      format: :plain,
      color: Keyword.get(opts, :color, :auto),
      width: Keyword.get(opts, :width, 80),
      registry: Keyword.get(opts, :registry)
    )
    |> Sink.render(diagnostic)
  end

  defp convert(reason, _file, _source) when is_struct(reason, Cure.Diagnostic) do
    {:ok, reason, nil}
  end

  defp convert(reason, file, source) do
    if operational_reason?(reason) do
      {:ok, Operational.from_error(reason), nil}
    else
      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, file, source)
      {:ok, diagnostic, registry}
    end
  rescue
    Cure.Diagnostic.UnhandledError ->
      {:ok, Operational.impossible_return(:unregistered_diagnostic, reason), nil}
  end

  defp read_source(file) do
    case File.read(file) do
      {:ok, source} -> source
      {:error, _reason} -> ""
    end
  end

  defp operational_reason?({:file_read_error, _, _}), do: true
  defp operational_reason?({:file_write_error, _, _}), do: true
  defp operational_reason?({:dependency_resolution_failed, _}), do: true
  defp operational_reason?({:command_failed, _, _}), do: true
  defp operational_reason?({:migration_warning, details}) when is_map(details), do: true
  defp operational_reason?({:compiler_warning, details}) when is_map(details), do: true
  defp operational_reason?({:export_unmappable, _}), do: true
  defp operational_reason?({:snap_missing, _}), do: true
  defp operational_reason?({:configuration_warning, _}), do: true
  defp operational_reason?({:usage_error, _}), do: true
  defp operational_reason?({:artifact_error, _}), do: true
  defp operational_reason?({:proof_file_missing, _}), do: true
  defp operational_reason?({:proof_verification_failed, _}), do: true
  defp operational_reason?({:proof_schema_incompatible, _}), do: true
  defp operational_reason?({:snap_schema_incompatible, _}), do: true
  defp operational_reason?({:registry_signature_invalid, _}), do: true
  defp operational_reason?({:transparency_log_unreachable, _}), do: true
  defp operational_reason?({:registry_fetch_failed, _}), do: true
  defp operational_reason?({:registry_hash_mismatch, _}), do: true
  defp operational_reason?({:registry_package_not_found, _}), do: true
  defp operational_reason?({:version_conflict, _, _}), do: true
  defp operational_reason?({:invalid_dependency, _}), do: true
  defp operational_reason?({:invalid_constraint, _, _}), do: true
  defp operational_reason?({:no_versions, _}), do: true
  defp operational_reason?({:dependency_clone_failed, _, _}), do: true
  defp operational_reason?({:dependency_edition_error, _, _}), do: true
  defp operational_reason?({:duplicate_app, _}), do: true
  defp operational_reason?({:app_name_mismatch, _, _}), do: true
  defp operational_reason?({:compile_failed, _}), do: true
  defp operational_reason?({:release_build_failed, _}), do: true
  defp operational_reason?({:release_app_missing, _, _}), do: true
  defp operational_reason?({:sys_config_read_failed, _, _}), do: true
  defp operational_reason?({:vm_args_read_failed, _, _}), do: true
  defp operational_reason?({:undocumented_public_function, _, _}), do: true
  defp operational_reason?(_), do: false
end
