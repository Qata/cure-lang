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

        # Add to code path
        File.mkdir_p!(output_dir)
        abs_dir = Path.expand(output_dir)

        unless abs_dir in :code.get_path() do
          :code.add_patha(String.to_charlist(abs_dir))
        end

        case Cure.Compiler.Incremental.compile_dir(cure_files, output_dir,
               source_roots: [stdlib_dir],
               compile_opts: [emit_events: false]
             ) do
          {:ok, summary} ->
            Enum.each(summary.cycles, fn walk ->
              Mix.shell().info(Cure.Diagnostic.Host.render({:import_cycle, walk}, stdlib_dir))
            end)

            Mix.shell().info(
              "  #{length(summary.compiled)} compiled, " <>
                "#{length(summary.skipped_fresh)} up-to-date, " <>
                "#{length(summary.deleted)} removed"
            )

            Mix.shell().info("  Output: #{output_dir}")

            unless summary.errors == [] do
              Enum.each(summary.errors, fn {target, reason} ->
                Mix.shell().error("  #{Cure.Diagnostic.Host.render(reason, target)}")
              end)

              exit({:shutdown, 1})
            end

          {:error, reason} ->
            Mix.shell().error(Cure.Diagnostic.Host.render(reason, stdlib_dir))
            exit({:shutdown, 1})
        end
    end
  end

  defp compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_file, 2)
  end
end
