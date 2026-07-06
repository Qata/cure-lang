defmodule Mix.Tasks.Cure.CompileStage1 do
  @moduledoc """
  Compiles the Cure stage1 compiler sources from `lib/compiler/**/*.cure`.

  Empty files are treated as placeholders and skipped. This lets the
  bootstrapped compiler tree exist in source control before every kernel
  module has a body, while still making every non-empty stage1 source part of
  the regular build.

  Test sources under `lib/compiler/**/tests/**/*.cure` are skipped by default.
  Pass `--include-tests` when those sources should be compiled as part of the
  same pass.

  ## Usage

      mix cure.compile_stage1
      mix cure.compile_stage1 --include-tests
      mix cure.compile_stage1 --output-dir path/to/ebin
  """

  use Mix.Task

  @shortdoc "Compiles Cure stage1 compiler sources"
  @recursive true

  @source_dir Path.join(["lib", "compiler"])

  @impl Mix.Task
  def run(args) do
    {opts, _, _} =
      OptionParser.parse(args,
        switches: [include_tests: :boolean, output_dir: :string],
        aliases: [o: :output_dir]
      )

    output_dir = Keyword.get(opts, :output_dir, "_build/cure/stage1/ebin")
    include_tests? = Keyword.get(opts, :include_tests, false)

    Mix.Task.run("app.start", ["--no-deps-check"])

    files =
      @source_dir
      |> Path.join("**/*.cure")
      |> Path.wildcard()
      |> Enum.sort_by(&stage1_sort_key/1)
      |> maybe_reject_tests(include_tests?)

    result =
      cond do
      not compiler_available?() ->
        Mix.shell().info("Cure.Compiler not yet available, skipping stage1 compilation")
        :ok

      files == [] ->
        Mix.shell().info("No .cure files found in #{@source_dir}")
        :ok

      true ->
        File.mkdir_p!(output_dir)
        Code.prepend_path(Path.expand(output_dir))

        results =
          Enum.map(files, fn path ->
            if blank_source?(path) do
              Mix.shell().info("  skip #{relative(path)}")
              {:skip, path}
            else
              compile_one(path, output_dir)
            end
          end)

        compiled = Enum.count(results, &match?({:ok, _}, &1))
        skipped = Enum.count(results, &match?({:skip, _}, &1))
        failed = Enum.filter(results, &match?({:error, _}, &1))

        Mix.shell().info("stage1: #{compiled} compiled, #{skipped} placeholders, #{length(failed)} errors")
        Mix.shell().info("stage1 output: #{output_dir}")

        if failed != [] do
          exit({:shutdown, 1})
        end

        :ok
      end

    Mix.Task.reenable("cure.compile_stage1")
    result
  end

  defp maybe_reject_tests(files, true), do: files

  defp maybe_reject_tests(files, false) do
    Enum.reject(files, fn path ->
      path
      |> Path.split()
      |> Enum.member?("tests")
    end)
  end

  defp stage1_sort_key(path) do
    relative = Path.relative_to_cwd(path)

    {stage1_group(relative), relative}
  end

  defp stage1_group("lib/compiler/kernel/core/name.cure"), do: 0
  defp stage1_group("lib/compiler/kernel/core/literal.cure"), do: 1
  defp stage1_group("lib/compiler/kernel/core/level.cure"), do: 2
  defp stage1_group("lib/compiler/kernel/core/syntax.cure"), do: 3
  defp stage1_group("lib/compiler/kernel/core/expr.cure"), do: 4
  defp stage1_group("lib/compiler/kernel/core/exception.cure"), do: 5
  defp stage1_group("lib/compiler/kernel/core/declaration.cure"), do: 6
  defp stage1_group("lib/compiler/kernel/core/local_context.cure"), do: 7
  defp stage1_group("lib/compiler/kernel/core/environment.cure"), do: 8
  defp stage1_group("lib/compiler/kernel/core/type_checker.cure"), do: 9
  defp stage1_group("lib/compiler/kernel/core/mod.cure"), do: 10
  defp stage1_group("lib/compiler/kernel/tests/" <> _), do: 90
  defp stage1_group(_), do: 50

  defp compile_one(path, output_dir) do
    Mix.shell().info("  compile #{relative(path)}")

    case Cure.Compiler.compile_file(path, output_dir: output_dir, emit_events: false) do
      {:ok, module, warnings} ->
        Enum.each(warnings, fn warning ->
          Mix.shell().info("    warning: #{inspect(warning)}")
        end)

        {:ok, module}

      {:error, reason} ->
        formatted = Cure.Compiler.Errors.format_error(reason, path)
        Mix.shell().error("    #{formatted}")
        {:error, path}
    end
  end

  defp blank_source?(path) do
    case File.read(path) do
      {:ok, source} -> String.trim(source) == ""
      {:error, _} -> false
    end
  end

  defp relative(path), do: Path.relative_to_cwd(path)

  defp compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_file, 2)
  end
end
