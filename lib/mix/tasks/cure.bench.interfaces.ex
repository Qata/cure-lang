defmodule Mix.Tasks.Cure.Bench.Interfaces do
  @moduledoc """
  Measure cold and cached runs through the canonical module pipeline.

      mix cure.bench.interfaces
      mix cure.bench.interfaces lib/std/regex.cure --warm-iterations 5
  """

  use Mix.Task

  @shortdoc "Benchmarks cold/warm canonical module checking"

  @impl Mix.Task
  def run(args) do
    {opts, paths, invalid} =
      OptionParser.parse(args, strict: [warm_iterations: :integer], aliases: [n: :warm_iterations])

    if invalid != [], do: Mix.raise("invalid arguments: #{inspect(invalid)}")

    paths = if paths == [], do: Path.wildcard("lib/std/**/*.cure"), else: paths
    iterations = Keyword.get(opts, :warm_iterations, 3)

    case Cure.Compiler.InterfaceBenchmark.run(paths, warm_iterations: iterations) do
      {:ok, report} -> print_report(report)
      {:error, reason} -> Mix.raise("interface benchmark failed: #{inspect(reason)}")
    end
  end

  defp print_report(report) do
    Mix.shell().info(
      "pipeline=#{report.pipeline} sources=#{report.source_count} " <>
        "cold_ms=#{ms(report.cold.total_us)} rebuilt=#{length(report.cold.rebuilt_modules)}"
    )

    Mix.shell().info("component_ms\tmodules")

    report.cold.components
    |> Enum.sort_by(&{-&1.elapsed_us, &1.modules})
    |> Enum.each(fn component ->
      Mix.shell().info("#{ms(component.elapsed_us)}\t#{Enum.join(component.modules, ",")}")
    end)

    report.warm
    |> Enum.with_index(1)
    |> Enum.each(fn {sample, index} ->
      Mix.shell().info(
        "warm_#{index}_ms=#{ms(sample.total_us)} rebuilt=#{length(sample.rebuilt_modules)} " <>
          "module_check_ms=#{ms(Map.get(sample.phases, :module_check, 0))}"
      )
    end)
  end

  defp ms(microseconds), do: :erlang.float_to_binary(microseconds / 1_000, decimals: 3)
end
