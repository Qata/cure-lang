defmodule Mix.Tasks.Cure.Check.Stdlib do
  @moduledoc """
  Regression task: compiles every `.cure` file in `lib/std/` and fails
  if any module fails to produce a `.beam` or emits a compiler warning.

  Invoke as:

      mix cure.check.stdlib

  This is intentionally stricter than `mix cure.compile_stdlib`:

  - any error is fatal,
  - any warning is fatal too (the stdlib must be warning-free so
    downstream programs can rely on clean `erl_lint` output).

  CI consumes the exit code to gate merges.
  """

  use Mix.Task

  alias Cure.Diagnostic.{Host, Sink}

  @shortdoc "Compile every Std.* module and reject errors or warnings"

  @stdlib_dir "lib/std"
  @output_dir "_build/cure/ebin"

  @impl Mix.Task
  def run(args) do
    if args != [] do
      usage_error("Usage: mix cure.check.stdlib")
    end

    Application.ensure_all_started(:cure)
    files = Path.wildcard(Path.join(@stdlib_dir, "*.cure")) |> Enum.sort()

    results =
      case Cure.Compiler.compile_files(files,
             output_dir: @output_dir,
             emit_events: false,
             source_roots: [@stdlib_dir],
             continue_on_error: true
           ) do
        {:ok, result} ->
          successes =
            Enum.map(result.compiled, fn {path, module, warnings} ->
              {path, {:ok, module, warnings}}
            end)

          failures = Enum.map(result.errors, fn {path, reason} -> {path, {:error, reason}} end)
          successes ++ failures

        {:error, reason} ->
          [{@stdlib_dir, {:error, reason}}]
      end

    results =
      Enum.map(results, fn {path, outcome} ->
        name = Path.basename(path, ".cure")

        case outcome do
          {:ok, module, []} ->
            IO.puts("  ok  #{pad(name)} -> #{module}")
            {:pass, name}

          {:ok, _module, warnings} ->
            IO.puts("  FAIL #{pad(name)} #{length(warnings)} compiler warning(s)")

            Enum.each(warnings, fn warning ->
              Mix.shell().error(render_host_diagnostic({:compiler_warning, warning}, path))
            end)

            {:fail, name}

          {:error, reason} ->
            IO.puts("  FAIL #{pad(name)} compilation failed")
            Mix.shell().error(render_host_diagnostic(reason, path))
            {:fail, name}
        end
      end)

    passed = Enum.count(results, &match?({:pass, _}, &1))
    failed = Enum.filter(results, &match?({:fail, _}, &1))

    if failed == [] do
      IO.puts("\nstdlib: #{passed} passed, 0 failed")
      :ok
    else
      IO.puts("\nstdlib: #{passed} passed, #{length(failed)} failed")
      exit({:shutdown, 1})
    end
  end

  defp pad(name), do: String.pad_trailing(name, 20)

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Host.to_diagnostic(reason, path)

    Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    diagnostic = Cure.Diagnostic.Operational.usage(message)

    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
    |> Mix.shell().error()

    exit({:shutdown, 1})
  end
end
