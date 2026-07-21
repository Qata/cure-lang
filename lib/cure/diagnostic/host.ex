defmodule Cure.Diagnostic.Host do
  @moduledoc "Single presentation boundary for compiler and host command output."

  alias Cure.Diagnostic.{Operational, Sink}

  @doc "Render a compiler or host failure with its authored source context."
  @spec render(term(), String.t(), String.t() | nil) :: String.t()
  def render(reason, file, source \\ nil) when is_binary(file) do
    {diagnostic, registry} = to_diagnostic(reason, file, source)

    Sink.new(format: :plain, registry: registry)
    |> Sink.render(diagnostic)
  end

  @doc "Convert a host or compiler failure without selecting an output format."
  @spec to_diagnostic(term(), String.t(), String.t() | nil) ::
          {Cure.Diagnostic.t(), Cure.Diagnostic.SourceRegistry.t() | nil}
  def to_diagnostic(reason, file, source \\ nil) when is_binary(file) do
    source = source || read_source(file)

    case convert(reason, file, source) do
      {:ok, diagnostic, registry} -> {diagnostic, registry}
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

  @doc "Emit a structured diagnostic through the shared sink."
  @spec emit_diagnostic(Cure.Diagnostic.t(), keyword()) :: {:ok, Sink.t()} | {:error, term()}
  def emit_diagnostic(%Cure.Diagnostic{} = diagnostic, opts \\ []) do
    Sink.new(
      format: :terminal,
      color: Keyword.get(opts, :color, :auto),
      width: Keyword.get(opts, :width, 80),
      output_device: Keyword.get(opts, :output_device, :standard_error),
      registry: Keyword.get(opts, :registry)
    )
    |> Sink.emit(diagnostic)
    |> Sink.flush()
  end

  defp convert(reason, _file, _source) when is_struct(reason, Cure.Diagnostic) do
    {:ok, reason, nil}
  end

  defp convert(reason, file, source) do
    if operational_reason?(reason) do
      diagnostic = Operational.from_error(reason)

      case source do
        source when is_binary(source) and byte_size(source) > 0 ->
          registry =
            Cure.Diagnostic.SourceRegistry.new()
            |> Cure.Diagnostic.SourceRegistry.register(file, source, file)

          {:ok, remap_operational_span(diagnostic, registry, file), registry}

        _ ->
          {:ok, diagnostic, nil}
      end
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

  defp remap_operational_span(
         %Cure.Diagnostic{primary: %Cure.Diagnostic.Label{span: %Cure.Diagnostic.Span{} = span} = label} =
           diagnostic,
         registry,
         source_id
       ) do
    case Cure.Diagnostic.SourceRegistry.span_at(registry, source_id, span.start_line, span.start_column, 0) do
      {:ok, remapped} -> %{diagnostic | primary: %{label | span: remapped}}
      {:error, _} -> diagnostic
    end
  end

  defp remap_operational_span(diagnostic, _registry, _source_id), do: diagnostic

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
  defp operational_reason?({:unknown_watch_action, _}), do: true
  defp operational_reason?({:file_error, _}), do: true
  defp operational_reason?({:decode_failed, _}), do: true
  defp operational_reason?({:parse, _}), do: true
  defp operational_reason?({:fetch_failed, _, _}), do: true
  defp operational_reason?({:hash_mismatch, _}), do: true
  defp operational_reason?({:package_not_found, _}), do: true
  defp operational_reason?({:unreachable, _}), do: true
  defp operational_reason?({:chain_broken, _}), do: true
  defp operational_reason?({:app_resource_write_failed, _, _}), do: true
  defp operational_reason?({:write_failed, _, _}), do: true
  defp operational_reason?({:load_failed, _}), do: true
  defp operational_reason?({:compilation_failed, _}), do: true
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
