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
      Mix.shell().error("Usage: mix cure.compile <path> [--output-dir DIR]")
      exit({:shutdown, 1})
    end

    # Ensure the application is started (for Registry)
    Mix.Task.run("app.start", [])

    files =
      paths
      |> Enum.flat_map(fn path ->
        if File.dir?(path), do: Path.wildcard(Path.join(path, "**/*.cure")), else: [path]
      end)
      |> Enum.uniq()

    case Cure.Compiler.prepare_files(files) do
      {:ok, %{ordered: ordered, providers: providers, cycles: cycles}} ->
        Enum.each(cycles, fn walk ->
          Mix.shell().info(Cure.Compiler.Errors.format_error({:import_cycle, walk}, hd(paths)))
        end)

        source_roots = files |> Enum.map(&Path.dirname/1) |> Enum.uniq()

        opts = [
          output_dir: output_dir,
          source_roots: source_roots,
          prelude_providers: providers
        ]

        Enum.each(ordered, &compile_one(&1, opts))

      {:error, reason} ->
        Mix.shell().error(Cure.Compiler.Errors.format_error(reason, hd(paths)))
        exit({:shutdown, 1})
    end
  end

  defp compile_one(path, opts) do
    Mix.shell().info("Compiling #{path}")

    case Cure.Compiler.compile_file(path, opts) do
      {:ok, module, warnings} ->
        Enum.each(warnings, fn w ->
          Mix.shell().info("  warning: #{inspect(w)}")
        end)

        Mix.shell().info("  -> #{module}")
        _ = Cure.Compiler.load_emitted(module, Keyword.fetch!(opts, :output_dir))

      {:error, reason} ->
        formatted = Cure.Compiler.Errors.format_error(reason, path)
        Mix.shell().error(formatted)
    end
  end
end
