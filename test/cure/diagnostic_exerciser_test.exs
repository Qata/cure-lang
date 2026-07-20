defmodule Cure.DiagnosticExerciserTest do
  use ExUnit.Case, async: false

  alias Cure.Diagnostic.{Operational, Renderer}

  test "exercises every public diagnostic family and shows user output" do
    diagnostics = [
      Operational.file_read("demo.cure", :enoent),
      Operational.file_write("demo.cure", :eacces),
      Operational.dependency(:locked),
      Operational.command_failure("compile", :failed),
      Operational.migration_warning(%{rule: :legacy, file: "demo.cure", line: 2, message: "migrate this"}),
      Operational.compiler_warning(%{file: "demo.cure", line: 3, message: "check this"}),
      Operational.export_unmappable("dependent type"),
      Operational.snap_missing("gone.cure"),
      Operational.configuration_warning("invalid setting"),
      Operational.usage("Usage: cure compile FILE"),
      Operational.artifact_error("artifact is invalid")
    ]

    Enum.each(diagnostics, fn diagnostic ->
      IO.puts(:stderr, Renderer.plain(diagnostic))
    end)

    assert Enum.map(diagnostics, & &1.code) == ~w[E095 E096 E097 E098 W001 W000 E068 E070 W002 E099 E100]
  end
end
