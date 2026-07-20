defmodule Cure.DiagnosticExerciserTest do
  use ExUnit.Case, async: false

  alias Cure.Diagnostic.{Operational, Renderer}

  defp render_options do
    config = Application.get_env(:cure, :diagnostics_exerciser, [])
    [color: Keyword.get(config, :color, :always), width: Keyword.get(config, :width, 80)]
  end

  test "exercises every public diagnostic family and shows user output" do
    compiler_cases = [
      {"unknown global", "E091", "mod DiagnosticUnknown\n  fn run() -> Int = missing_name\n"},
      {"syntax error", "E094", "mod DiagnosticSyntax\n  fn run(] -> Int = 1\n"},
      {"type mismatch", "E093",
       "mod DiagnosticType\n  type Nat = Z | S(Nat)\n  fn bad() -> Equivalent(Nat, Z, S(Z)) = reflexive(Z)\n"},
      {"unfilled hole", "E014", "mod DiagnosticHole\n  fn bad() -> Int = ???\n"},
      {"unterminated lambda", "E035", "fn (x) -> x; x;"}
    ]

    compiler_codes = Enum.map(compiler_cases, &elem(&1, 1))

    Enum.each(compiler_cases, fn {label, expected_code, source} ->
      case Cure.Compiler.compile_string(source, emit_events: false) do
        {:ok, module, warnings} ->
          flunk("#{label} unexpectedly compiled as #{inspect(module)} with #{length(warnings)} warning(s)")

        {:error, reason} ->
          {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "#{label}.cure", source)
          assert diagnostic.code == expected_code
          assert diagnostic.primary, "#{label} did not retain an authored source span"
          plain = Renderer.plain(diagnostic, registry)
          assert plain =~ " | ", "#{label} did not render an authored source excerpt"

          terminal =
            Renderer.terminal(
              diagnostic,
              registry,
              Keyword.merge(render_options(), output_device: :standard_error)
            )

          assert Enum.any?(String.split(source, "\n"), &(&1 != "" and String.contains?(terminal, &1)))
          IO.puts(:stderr, "[#{label}]\n" <> terminal)
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
      IO.puts(
        :stderr,
        Renderer.terminal(
          diagnostic,
          nil,
          Keyword.merge(render_options(), output_device: :standard_error)
        )
      )
    end)

    operational_codes = Enum.map(diagnostics, & &1.code)
    assert operational_codes == ~w[E095 E096 E097 E098 W001 W000 E068 E070 W002 E099 E100]

    registered_codes = Cure.Compiler.Errors.list_all() |> Enum.map(&elem(&1, 0)) |> MapSet.new()
    covered_codes = MapSet.new(compiler_codes ++ operational_codes)
    missing_codes = MapSet.difference(registered_codes, covered_codes) |> Enum.sort()

    IO.puts(
      :stderr,
      "\nDIAGNOSTIC PATH COVERAGE: #{MapSet.size(covered_codes)}/#{MapSet.size(registered_codes)} registered codes"
    )

    IO.puts(:stderr, "UNCOVERED REGISTERED CODES: " <> Enum.join(missing_codes, ", "))
    assert MapSet.subset?(covered_codes, registered_codes)

    if Keyword.get(Application.get_env(:cure, :diagnostics_exerciser, []), :coverage, false) do
      assert missing_codes == [], "diagnostic coverage is incomplete"
    end
  end
end
