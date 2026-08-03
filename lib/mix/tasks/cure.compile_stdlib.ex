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

        progress_key = {__MODULE__, make_ref()}
        diagnostics_key = {__MODULE__, make_ref()}
        Process.put(progress_key, %{count: 0, seen: MapSet.new()})
        Process.put(diagnostics_key, [])

        progress = fn {:compile_started, module, _path} ->
          %{count: count, seen: seen} = Process.get(progress_key)

          if MapSet.member?(seen, module) do
            Mix.shell().info("  [recheck] #{module}")
          else
            current = count + 1
            Process.put(progress_key, %{count: current, seen: MapSet.put(seen, module)})
            Mix.shell().info("  [#{current}/#{length(cure_files)}] #{module}")
          end
        end

        collect_diagnostics = fn diagnostics, registry ->
          Process.put(
            diagnostics_key,
            [{diagnostics, registry} | Process.get(diagnostics_key, [])]
          )
        end

        {result, diagnostic_batches} =
          try do
            result =
              Cure.Compiler.Artifacts.sweep(
                source_roots: [stdlib_dir],
                output_dir: output_dir,
                kind: :stdlib,
                repair: true,
                progress: progress,
                migration_diagnostic_sink: collect_diagnostics,
                compile_opts: [emit_events: false]
              )

            {result, diagnostics_key |> Process.get([]) |> Enum.reverse()}
          after
            Process.delete(progress_key)
            Process.delete(diagnostics_key)
          end

        flush_migration_diagnostics(diagnostic_batches)

        case result do
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

  defp flush_migration_diagnostics(batches) do
    Enum.each(batches, fn {diagnostics, registry} ->
      sink =
        Cure.Diagnostic.Sink.new(
          registry: registry,
          format: :plain,
          output_device: :stderr,
          width: 80
        )

      sink
      |> Cure.Diagnostic.Sink.emit_all(diagnostics)
      |> Cure.Diagnostic.Sink.flush()
    end)
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
