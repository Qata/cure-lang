defmodule Cure.DiagnosticExerciserTest do
  use ExUnit.Case, async: false

  alias Cure.Diagnostic.{Operational, Renderer}

  test "exercises every public diagnostic family and shows user output" do
    compiler_cases = [
      {"unknown global", "E091", "mod DiagnosticUnknown\n  fn run() -> Int = missing_name\n"},
      {"syntax error", "E094", "mod DiagnosticSyntax\n  fn run(] -> Int = 1\n"},
      {"type mismatch", "E093",
       "mod DiagnosticType\n  type Nat = Z | S(Nat)\n  fn bad() -> Equivalent(Nat, Z, S(Z)) = reflexive(Z)\n"}
    ]

    Enum.each(compiler_cases, fn {label, expected_code, source} ->
      case Cure.Compiler.compile_string(source, emit_events: false) do
        {:ok, module, warnings} ->
          flunk("#{label} unexpectedly compiled as #{inspect(module)} with #{length(warnings)} warning(s)")

        {:error, reason} ->
          {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "#{label}.cure", source)
          assert diagnostic.code == expected_code
          assert diagnostic.primary, "#{label} did not retain an authored source span"
          rendered = Renderer.plain(diagnostic, registry)
          assert rendered =~ " | ", "#{label} did not render an authored source excerpt"
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
