defmodule Cure.Diagnostic.Operational do
  @moduledoc "Explicit diagnostics for failures outside elaboration."

  alias Cure.Diagnostic

  @doc "Convert an operational failure tuple at a host boundary."
  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, _opts \\ [])

  def from_error({:file_read_error, path, reason}, _opts), do: file_read(path, reason)
  def from_error({:file_write_error, path, reason}, _opts), do: file_write(path, reason)
  def from_error({:dependency_resolution_failed, reason}, _opts), do: dependency(reason)
  def from_error({:command_failed, command, reason}, _opts), do: command_failure(command, reason)
  def from_error({:migration_warning, details}, _opts) when is_map(details), do: migration_warning(details)
  def from_error({:compiler_warning, details}, _opts) when is_map(details), do: compiler_warning(details)
  def from_error({:export_unmappable, reason}, _opts), do: export_unmappable(reason)
  def from_error({:snap_missing, path}, _opts), do: snap_missing(path)
  def from_error({:configuration_warning, message}, _opts), do: configuration_warning(message)
  def from_error({:usage_error, message}, _opts), do: usage(message)
  def from_error({:artifact_error, message}, _opts), do: artifact_error(message)
  def from_error({:proof_file_missing, detail}, _opts), do: proof_file_missing(detail)
  def from_error({:proof_verification_failed, detail}, _opts), do: proof_verification_failed(detail)
  def from_error({:proof_schema_incompatible, detail}, _opts), do: proof_schema_incompatible(detail)
  def from_error({:snap_schema_incompatible, detail}, _opts), do: snap_schema_incompatible(detail)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  def file_read(path, reason),
    do:
      diagnostic("E095", :file_read, "Cannot read `#{path}`: #{file_reason(reason)}", %{
        path: path,
        reason: inspect(reason)
      })

  def file_write(path, reason),
    do:
      diagnostic("E096", :file_write, "Cannot write `#{path}`: #{file_reason(reason)}", %{
        path: path,
        reason: inspect(reason)
      })

  def dependency(reason),
    do:
      diagnostic("E097", :dependency_resolution, "Failed to resolve dependencies: #{file_reason(reason)}", %{
        reason: inspect(reason)
      })

  def command_failure(command, reason),
    do:
      diagnostic("E098", :command_failure, "#{command} failed: #{file_reason(reason)}", %{
        command: command,
        reason: inspect(reason)
      })

  def migration_warning(%{rule: rule, file: file, line: line, message: message}) do
    Diagnostic.new(
      code: "W001",
      key: :migration_warning,
      severity: :warning,
      title: "Migration warning",
      message: message,
      primary: %Cure.Diagnostic.Label{
        span: %Cure.Diagnostic.Span{
          source_id: file,
          path: file,
          start_byte: 0,
          end_byte: 0,
          start_line: line || 1,
          end_line: line || 1,
          start_column: 1,
          end_column: 1
        },
        style: :primary,
        message: "rule #{rule} applies here"
      },
      payload: %{rule: rule, file: file, line: line}
    )
  end

  def compiler_warning(%{file: file, line: line, message: message}) do
    Diagnostic.new(
      code: "W000",
      key: :compiler_warning,
      severity: :warning,
      title: "Compiler warning",
      message: message,
      payload: %{file: file, line: line}
    )
  end

  def export_unmappable(reason),
    do: diagnostic("E068", :export_type_unmappable, "Export type cannot be represented: #{reason}", %{reason: reason})

  def snap_missing(path),
    do: diagnostic("E070", :snap_path_missing, "Snap loaded path no longer exists: #{path}", %{path: path})

  def configuration_warning(message), do: diagnostic("W002", :configuration_warning, message, %{})
  def usage(message), do: diagnostic("E099", :usage_error, message, %{})
  def artifact_error(message), do: diagnostic("E100", :artifact_error, message, %{})

  def proof_file_missing(detail),
    do: diagnostic("E065", :proof_file_missing, "Proof file is missing: #{detail}", %{detail: detail})

  def proof_verification_failed(detail),
    do: diagnostic("E066", :proof_verification_failed, "Proof verification failed: #{detail}", %{detail: detail})

  def proof_schema_incompatible(detail),
    do: diagnostic("E067", :proof_schema_incompatible, "Proof schema is incompatible: #{detail}", %{detail: detail})

  def snap_schema_incompatible(detail),
    do: diagnostic("E069", :snap_schema_incompatible, "Snap schema is incompatible: #{detail}", %{detail: detail})

  @doc "Build E101 only for a caught exception at an explicit compiler boundary."
  def internal_exception(exception, stacktrace, opts \\ []) when is_exception(exception) and is_list(stacktrace) do
    fingerprint = fingerprint({exception.__struct__, Exception.message(exception), stack_head(stacktrace)})

    payload = %{
      fingerprint: fingerprint,
      exception: inspect(exception.__struct__),
      context: Keyword.get(opts, :context)
    }

    payload = if Keyword.get(opts, :debug, false), do: Map.put(payload, :stacktrace, stacktrace), else: payload

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Internal compiler error",
      message: "The compiler failed unexpectedly. Please report fingerprint `#{fingerprint}`.",
      payload: payload
    )
  end

  @doc "Build E101 for a return shape that violates an internal boundary contract."
  def impossible_return(context, value, opts \\ []) do
    fingerprint = fingerprint({context, value})

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Internal compiler error",
      message: "The compiler reached an impossible state. Please report fingerprint `#{fingerprint}`.",
      payload: %{
        fingerprint: fingerprint,
        context: context,
        impossible_shape: if(Keyword.get(opts, :debug, false), do: inspect(value), else: nil)
      }
    )
  end

  defp diagnostic(code, key, message, payload) do
    Diagnostic.new(
      code: code,
      key: key,
      severity: if(String.starts_with?(code, "W"), do: :warning, else: :error),
      title: title(key),
      message: message,
      payload: payload
    )
  end

  defp title(:file_read), do: "Could not read file"
  defp title(:file_write), do: "Could not write file"
  defp title(:dependency_resolution), do: "Dependency resolution failed"
  defp title(:command_failure), do: "Command failed"
  defp title(:export_type_unmappable), do: "Type cannot cross this boundary"
  defp title(:snap_path_missing), do: "Saved path is missing"
  defp title(:configuration_warning), do: "Invalid configuration"
  defp title(:usage_error), do: "Invalid command usage"
  defp title(:artifact_error), do: "Invalid build artifact"
  defp title(:proof_file_missing), do: "Proof file missing"
  defp title(:proof_verification_failed), do: "Proof verification failed"
  defp title(:proof_schema_incompatible), do: "Proof schema incompatible"
  defp title(:snap_schema_incompatible), do: "Snap schema incompatible"

  defp fingerprint(term) do
    term
    |> :erlang.term_to_binary()
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
    |> binary_part(0, 12)
  end

  defp stack_head([{module, function, arity, location} | _]), do: {module, function, arity, location}
  defp stack_head(_), do: nil

  defp file_reason(reason) when is_atom(reason), do: :file.format_error(reason)
  defp file_reason({kind, detail}) when is_atom(kind), do: "#{kind}: #{file_reason(detail)}"
  defp file_reason(reason) when is_binary(reason), do: reason
  defp file_reason(reason), do: inspect(reason)
end
