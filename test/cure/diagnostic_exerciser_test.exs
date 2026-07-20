defmodule Cure.DiagnosticExerciserTest do
  use ExUnit.Case, async: false

  alias Cure.Diagnostic.{Operational, Renderer}

  test "exercises every public diagnostic family and shows user output" do
    compiler_cases = [
      {"unknown global", "mod DiagnosticUnknown\n  fn run() -> Int = missing_name\n"},
      {"syntax error", "mod DiagnosticSyntax\n  fn run( -> Int = 1\n"},
      {"type mismatch", "mod DiagnosticType\n  fn run() -> Int = \"not an int\"\n"}
    ]

    Enum.each(compiler_cases, fn {label, source} ->
      case Cure.Compiler.compile_string(source, emit_events: false) do
        {:ok, _module, warnings} ->
          Enum.each(warnings, fn warning ->
            IO.puts(:stderr, "[#{label}] " <> Renderer.plain(Operational.compiler_warning(warning)))
          end)

        {:error, reason} ->
          rendered = Cure.Compiler.Errors.format_with_source(reason, "#{label}.cure", source)
          IO.puts(:stderr, "[#{label}]\n" <> rendered)
      end
    end)

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
