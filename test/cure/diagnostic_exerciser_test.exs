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
      {"unterminated lambda", "E035", "fn (x) -> x; x;"},
      {"unrecognized pattern", "E090",
       "mod DiagnosticPattern\n  fn bad(x: Int) -> Int = match x\n    1..10 -> 1\n    _ -> 0\n"},
      {"missing implicit", "E011", "mod DiagnosticImplicit\n  fn bad() -> Int = reflexive()\n"},
      {"unknown pattern constructor", "E091",
       "mod DiagnosticCtor\n  type Nat = Z | S(Nat)\n  fn bad(x: Nat) -> Nat = match x\n    Missing() -> Z\n    _ -> Z\n"},
      {"pickup without else", "E076", "mod DiagnosticPickupNoElse\n  fn bad(x: Int) -> Int = pickup\n    x > 0 -> 1\n"},
      {"pickup else not last", "E077",
       "mod DiagnosticPickupElseLast\n  fn bad(x: Int) -> Int = pickup\n    else -> 1\n    x > 0 -> 2\n"},
      {"pickup multiple else", "E078",
       "mod DiagnosticPickupMultipleElse\n  fn bad(x: Int) -> Int = pickup\n    else -> 1\n    else -> 2\n"},
      {"record field mismatch", "E022",
       "mod DiagnosticRecord\n  type Nat = Z | S(Nat)\n  rec Point\n    x: Nat\n    y: Nat\n  fn bad() -> Point = Point{x: S(Z()), z: Z()}\nend\n"}
    ]

    boundary_cases = [
      {"unbound variable", "E002", {:unbound_variable, "x is not bound", [line: 1, col: 17]}},
      {"arity mismatch", "E003", {:arity_mismatch, "expected 2 arguments", [line: 1, col: 17]}},
      {"extern untyped head", "E056", {:extern_untyped_head, "parameter is untyped", [line: 1, col: 1]}},
      {"extern has body", "E057", {:extern_has_body, "body is not allowed", [line: 1, col: 1]}},
      {"proof shape mismatch", "E026", {:proof_shape_mismatch, "not a proof", "bad"}},
      {"totality failure", "E013", {:totality_required, :loop}},
      {"pickup without else", "E076", {:pickup_no_else, "missing else", [line: 1, col: 1]}},
      {"pickup else not last", "E077", {:pickup_else_not_last, "else is not last", [line: 1, col: 1]}},
      {"pickup multiple else", "E078", {:pickup_multiple_else, "multiple else", [line: 1, col: 1]}},
      {"duplicate module", "E087", {:duplicate_module_identity, "Demo", "a.cure", "b.cure"}},
      {"ambiguous name", "E089", {:ambiguous_name, :helper, ["Demo.A", "Demo.B"]}},
      {"import cycle", "W086", {:import_cycle, [%{module: "Demo.A", path: "a.cure", line: 1}]}},
      {"unresolved import", "W088", {:unresolved_import, :helper, 1, ["Demo.A"], 2}},
      {"recovered parse", "E063", {:parse_recovered, :semicolon, 1, 1}},
      {"macro expansion", "E092",
       {:lift_module_error,
        %{module: "Demo.Generated", cause: {:unknown_global, :missing}, source_provenance: %{macro: :spawn}}}}
    ]

    compiler_codes = Enum.map(compiler_cases ++ boundary_cases, &elem(&1, 1))

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

          assert Cure.Compiler.Errors.format_with_source(reason, "#{label}.cure", source) =~ expected_code,
                 "#{label} still uses the legacy formatter path"

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

    Enum.each(boundary_cases, fn {label, expected_code, reason} ->
      {diagnostic, _registry} =
        Cure.Compiler.Errors.to_diagnostic(reason, "#{label}.cure", "fn run() -> Int = 1\n")

      assert diagnostic.code == expected_code
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
      Operational.proof_file_missing("demo.cureproof"),
      Operational.proof_verification_failed("Demo#lemma"),
      Operational.proof_schema_incompatible("version 2"),
      Operational.snap_schema_incompatible("version 9"),
      Operational.registry_signature_invalid("Demo@1.0.0"),
      Operational.transparency_log_unreachable(:econnrefused),
      Operational.configuration_warning("invalid setting"),
      Operational.usage("Usage: cure compile FILE"),
      Operational.artifact_error("artifact is invalid"),
      Operational.internal_exception(%ArgumentError{message: "boom"}, [])
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

    assert operational_codes ==
             ~w[E095 E096 E097 E098 W001 W000 E068 E070 E065 E066 E067 E069 E041 E042 W002 E099 E100 E101]

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
