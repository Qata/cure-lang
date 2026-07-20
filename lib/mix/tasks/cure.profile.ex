defmodule Mix.Tasks.Cure.Profile do
  @moduledoc """
  Profile the compilation of a Cure source file.

  Shows timing data per pipeline stage and event counts.

  ## Usage

      mix cure.profile path/to/file.cure
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Profile compilation of a Cure source file"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start", [])

    case args do
      [path | _] ->
        case Cure.Profiler.profile_file(path) do
          {:ok, report} ->
            IO.puts(Cure.Profiler.format_report(report))

          {:error, reason} ->
            Mix.shell().error(render_diagnostic(Cure.Diagnostic.Operational.command_failure("profile", reason)))
        end

      [] ->
        Mix.shell().error("Usage: mix cure.profile <file.cure>")
    end
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end
end
