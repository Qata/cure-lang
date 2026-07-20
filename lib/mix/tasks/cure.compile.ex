defmodule Mix.Tasks.Cure.Compile do
  @moduledoc """
  Compiles Cure source files to BEAM bytecode.

  ## Usage

      mix cure.compile path/to/file.cure
      mix cure.compile path/to/directory/

  ## Options

  - `--output-dir` -- directory for `.beam` output (default: `_build/cure/ebin`)
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  @shortdoc "Compiles Cure source files to BEAM bytecode"

  @impl Mix.Task
  def run(args) do
    {opts, paths, _} =
      OptionParser.parse(args,
        switches: [output_dir: :string],
        aliases: [o: :output_dir]
      )

    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")

    if paths == [] do
      Mix.shell().error(
        render_diagnostic(Cure.Diagnostic.Operational.usage("Usage: mix cure.compile <path> [--output-dir DIR]"))
      )

      exit({:shutdown, 1})
    end

    # Ensure the application is started (for Registry)
    Mix.Task.run("app.start", [])

    Enum.each(paths, fn path ->
      if File.dir?(path) do
        compile_dir(path, output_dir)
      else
        compile_one(path, output_dir)
      end
    end)
  end

  defp compile_dir(path, output_dir) do
    files = path |> Path.join("**/*.cure") |> Path.wildcard()

    case Cure.Compiler.Incremental.compile_dir(files, output_dir,
           source_roots: [path],
           stdlib_hash: Cure.Compiler.Incremental.stdlib_fingerprint()
         ) do
      {:ok, summary} ->
        Enum.each(summary.cycles, fn walk ->
          Mix.shell().info(Cure.Diagnostic.Host.render({:import_cycle, walk}, path))
        end)

        Mix.shell().info(
          "  #{length(summary.compiled)} compiled, " <>
            "#{length(summary.skipped_fresh)} up-to-date, " <>
            "#{length(summary.deleted)} removed"
        )

        unless summary.errors == [] do
          Enum.each(summary.errors, fn {target, reason} ->
            Mix.shell().error("  #{Cure.Diagnostic.Host.render(reason, target)}")
          end)

          exit({:shutdown, 1})
        end

      {:error, reason} ->
        Mix.shell().error(Cure.Diagnostic.Host.render(reason, path))
        exit({:shutdown, 1})
    end
  end

  defp compile_one(path, output_dir) do
    Mix.shell().info("Compiling #{path}")

    case Cure.Compiler.compile_file(path, output_dir: output_dir) do
      {:ok, module, warnings} ->
        Enum.each(warnings, fn w ->
          Mix.shell().info("  " <> render_diagnostic(Cure.Diagnostic.Operational.compiler_warning(w)))
        end)

        Mix.shell().info("  -> #{module}")

      {:error, reason} ->
        formatted = Cure.Diagnostic.Host.render(reason, path)
        Mix.shell().error(formatted)
    end
  end

  defp render_diagnostic(diagnostic) do
    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
  end
end
