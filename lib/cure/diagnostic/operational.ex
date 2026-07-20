defmodule Cure.Diagnostic.Operational do
  @moduledoc "Explicit diagnostics for failures outside elaboration."

  alias Cure.Diagnostic

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

  defp diagnostic(code, key, message, payload),
    do: Diagnostic.new(code: code, key: key, severity: :error, title: "#{key}", message: message, payload: payload)

  defp file_reason(reason) when is_atom(reason), do: :file.format_error(reason)
  defp file_reason({kind, detail}) when is_atom(kind), do: "#{kind}: #{file_reason(detail)}"
  defp file_reason(reason) when is_binary(reason), do: reason
  defp file_reason(reason), do: inspect(reason)
end
