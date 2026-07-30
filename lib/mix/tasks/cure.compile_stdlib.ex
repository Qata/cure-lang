defmodule Mix.Tasks.Cure.CompileStdlib do
  @moduledoc """
  Compiles the Cure standard library from `lib/std/*.cure` to BEAM bytecode.

  The compiled `.beam` files are placed in `_build/cure/ebin/` (or the
  directory given by `--output-dir`) and added to the Erlang code path so
  they can be used by Cure programs at runtime.

  ## Usage

      mix cure.compile_stdlib
      mix cure.compile_stdlib --output-dir path/to/ebin
  """

  use Mix.Task

  @shortdoc "Compiles the Cure standard library"

  @impl Mix.Task
  def run(args) do
    {opts, _, _} =
      OptionParser.parse(args,
        switches: [output_dir: :string],
        aliases: [o: :output_dir]
      )

    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")

    # Ensure the application is started (for Registry).
    # --no-deps-check prevents dependency-validation loops when
    # cure is compiled as a path dependency (env: :prod by default).
    Mix.Task.run("app.start", ["--no-deps-check"])

    stdlib_dir = Path.join(["lib", "std"])
    cure_files = Path.wildcard(Path.join(stdlib_dir, "*.cure"))

    cond do
      not compiler_available?() ->
        Mix.shell().info("Cure.Compiler not yet available, skipping stdlib compilation")
        :ok

      cure_files == [] ->
        Mix.shell().info("No .cure files found in #{stdlib_dir}")
        :ok

      true ->
        Mix.shell().info("Compiling Cure standard library (#{length(cure_files)} modules)")

        File.mkdir_p!(output_dir)

        case Cure.Compiler.Artifacts.sweep(
               source_roots: [stdlib_dir],
               output_dir: output_dir,
               kind: :stdlib,
               repair: true,
               compile_opts: [emit_events: false]
             ) do
          {:ok, result} ->
            Enum.each(result.cycles, fn walk ->
              Mix.shell().error(render_host_diagnostic({:import_cycle, walk}, stdlib_dir))
            end)

            Mix.shell().info(
              "  #{map_size(result.rebuilt)} compiled, " <>
                "#{length(result.reused)} up-to-date, " <>
                "#{map_size(result.removed)} removed"
            )

            Mix.shell().info("  Output: #{output_dir}")

          {:error, reason} ->
            render_sweep_error(reason, cure_files, stdlib_dir)
            exit({:shutdown, 1})
        end
    end
  end

  defp compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_file, 2)
  end

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path)

    Cure.Diagnostic.Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Cure.Diagnostic.Sink.render(diagnostic)
  end

  defp source_path_for(target, files) do
    if File.exists?(target) do
      target
    else
      module = target |> to_string() |> String.split(".") |> List.last()
      stem = Macro.underscore(module)

      Enum.find(files, target, fn path ->
        basename = Path.basename(path, ".cure")
        basename == stem or String.ends_with?(basename, "_" <> stem)
      end)
    end
  end

  defp render_sweep_error({:artifact_sweep_failed, errors}, files, _default) do
    Enum.each(errors, fn {target, reason} ->
      Mix.shell().error(render_host_diagnostic(reason, source_path_for(target, files)))
    end)
  end

  defp render_sweep_error(reason, _files, default) do
    Mix.shell().error(render_host_diagnostic(reason, default))
  end
end
