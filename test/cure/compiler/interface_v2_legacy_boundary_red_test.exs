defmodule Cure.Compiler.InterfaceV2LegacyBoundaryRedTest do
  use ExUnit.Case, async: true

  @moduletag :interface_v2_red

  @forbidden [
    {"env_with_generated_dependencies", "stamped-AST dependency recovery"},
    {":code.is_loaded(module)", "loaded-BEAM semantic resolution"},
    {"compile_missing_from_sources", "recursive source/provider compilation"}
  ]

  @semantic_boundary_files [
    "lib/cure/elab/program.ex",
    "lib/cure/stdlib/preload.ex"
  ]

  test "the interface-v2 semantic pipeline has no legacy resolution backdoors" do
    offenders =
      for path <- source_files(),
          {needle, reason} <- @forbidden,
          occurrence <- occurrences(path, needle),
          do: %{path: path, line: occurrence.line, call: needle, reason: reason}

    assert offenders == [], """
    interface-v2 must not depend on legacy semantic resolution paths.
    Remove these calls while replacing their behavior with manifest/interface contracts:

    #{Enum.map_join(offenders, "\n", &"  #{&1.path}:#{&1.line} #{&1.call} — #{&1.reason}")}
    """
  end

  defp source_files do
    Enum.filter(@semantic_boundary_files, &File.regular?/1)
  end

  defp occurrences(path, needle) do
    path
    |> File.stream!()
    |> Stream.with_index(1)
    |> Enum.flat_map(fn {line, line_number} ->
      if String.contains?(line, needle), do: [%{line: line_number}], else: []
    end)
  end
end
