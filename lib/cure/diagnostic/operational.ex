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

  defp diagnostic(code, key, message, payload),
    do: Diagnostic.new(code: code, key: key, severity: :error, title: "#{key}", message: message, payload: payload)

  defp file_reason(reason) when is_atom(reason), do: :file.format_error(reason)
  defp file_reason({kind, detail}) when is_atom(kind), do: "#{kind}: #{file_reason(detail)}"
  defp file_reason(reason) when is_binary(reason), do: reason
  defp file_reason(reason), do: inspect(reason)
end
