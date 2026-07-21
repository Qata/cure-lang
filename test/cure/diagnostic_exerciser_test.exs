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
      {"unknown record", "E021", {:unknown_record, :Missing}},
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
        %{module: "Demo.Generated", cause: {:unknown_global, :missing}, source_provenance: %{macro: :spawn}}}},
      {"erasure violation", "E102", {:unknown_erasure_class, :Handle, :banana}},
      {"positivity rejection", "E103", {:non_strictly_positive, :Bad}},
      {"relevance rejection", "E104", {:erased_used_relevantly, %{binder: 0, site: :returned}}},
      {"declaration conflict", "E105", {:duplicate_type, :Widget}},
      {"missing interface", "E091", {:no_such_interface, :Missing}},
      {"missing interface method", "E105", {:missing_method, :Eq, :compare}},
      {"union runtime collision", "E105", {:same_runtime_shape, [:Left, :Right]}},
      {"deriving failure", "E105", {:cannot_derive, :Show}},
      {"kernel index mismatch", "E093", {:index_mismatch, :different_index}},
      {"kernel inference hole", "E093", {:hole_in_inference_position, "h"}},
      {"constructor needs checking", "E093", {:ctor_requires_checking_mode, :Nat}},
      {"non-concrete bound", "E093", {:bounded_bound_not_concrete, {:var, 0}}},
      {"cyclic type aliases", "E105", {:cyclic_typealiases, ["A", "B", "A"]}},
      {"module identity missing", "E095", {:module_identity_missing, "demo.cure"}},
      {"character bound missing", "E093", {:char_literal_needs_bounded, 97}},
      {"character range failure", "E093", {:char_literal_out_of_range, 0x110000}},
      {"extern returns union", "E093", {:extern_returns_union, :foreign, {:union, []}}},
      {"dependent match inference", "E093", {:cannot_infer_dependent_match, :branch}},
      {"erased field inference", "E093", {:bidirectional_erased_field, :Ctor}},
      {"unbound kernel variable", "E091", {:unbound_var, :missing}},
      {"unknown type family", "E091", {:unknown_family, :Missing}},
      {"unknown constructor", "E091", {:unknown_ctor, :Missing}},
      {"foreign constructor", "E091", {:foreign_ctor, :Missing}},
      {"missing primitive builtin", "E092", {:primitive_missing_builtin, :Int}},
      {"unknown primitive tag", "E092", {:unknown_primitive_tag, :future_primitive}},
      {"primitive floor mismatch", "E092", {:primitive_floor_mismatch, :Int, :node, :floor}},
      {"unsupported declaration", "E092", {:unsupported_declaration, :future_declaration}},
      {"generated hole validation", "E092", {:generated_hole_not_well_typed, :term}},
      {"duplicate macro unit", "E092", {:duplicate_unit, "ms"}},
      {"overload has no match", "E093", {:no_matching_overload, :map, [:Int, :String]}},
      {"projection is not a record", "E093", {:projection_not_a_record, :Int}},
      {"typed pattern arity", "E003", {:typed_pattern_arity, 2}},
      {"unsupported expression", "E093", {:unsupported_expression, :unknown_form}},
      {"occurs check", "E093", {:occurs_check, 1, {:var, 1}}},
      {"forced pattern mismatch", "E093", {:source_context, {:forced_pattern_mismatch, :Int, :String}, %{}}},
      {"macro family failure", "E092", {:invalid_macro_family, {:syntax_family_cycle, ["A", "B", "A"]}, 1, 1}},
      {"missing stdlib source", "E095", {:missing_stdlib_source, "Std.Missing", "/tmp/Std/Missing.cure"}},
      {"operator conflict", "E106", {:builtin_operator_not_overloadable, :|>}},
      {"unsupported async", "E107", {:unsupported_async, "async primitive is unavailable", [line: 2]}},
      {"splice outside quote", "E108", {:splice_outside_quote, :splice, [line: 2]}},
      {"beam write failure", "E096", {:write_failed, "_build/Demo.beam", :eacces}},
      {"beam load failure", "E098", {:load_failed, :badfile}},
      {"beam compilation failure", "E098", {:compilation_failed, [{:bad_form, :detail}]}},
      {"invalid macro unit", "E092", {:invalid_unit, "ms"}},
      {"unknown macro unit", "E092", {:unknown_unit, "ms"}},
      {"invalid board name", "E092", {:invalid_board_name, 42}},
      {"invalid board pins", "E092", :invalid_board_pins},
      {"invalid board capabilities", "E092", :invalid_board_capabilities},
      {"invalid board buses", "E092", :invalid_board_buses},
      {"invalid board flash", "E092", :invalid_board_flash},
      {"board flash offset", "E092", :flash_offset_out_of_bounds},
      {"unsupported macro hole arity", "E092", {:unsupported_hole_arity, 3}},
      {"invalid Core grade", "E100", {:bad_grade, :not_a_grade}},
      {"unknown Core symbol", "E100", {:unknown_symbol, "not_loaded"}},
      {"ill-formed Core term", "E100", {:ill_formed_term, {:not_core, 1}}},
      {"unregistered bounded family", "E093", :bounded_family_unregistered},
      {"reachable absurd branch", "E093", :absurd_in_reachable_position},
      {"opaque elimination", "E093", :opaque_not_eliminable},
      {"non-data case", "E093", :case_scrutinee_not_data},
      {"non-total definition", "E093", :not_total},
      {"non-function application", "E093", :not_a_function},
      {"non-exhaustive pattern", "E093", :coverage},
      {"branch arity", "E093", :branch_arity},
      {"branch type", "E093", :branch_type},
      {"index arity", "E093", :index_arity},
      {"applied non-function", "E093", :applied_non_function},
      {"rewrite expected type", "E093", :rewrite_requires_expected_type},
      {"rewrite proof", "E093", :rewrite_proof_not_equality},
      {"match non-data", "E093", :match_scrutinee_not_data},
      {"mixed rematch arms", "E093", :with_mixed_rematch_arms},
      {"with non-data", "E093", :with_scrutinee_not_data},
      {"too few arguments", "E093", :too_few_arguments},
      {"too many arguments", "E093", :too_many_arguments},
      {"non-variable scrutinee", "E093", :nonvariable_scrutinee},
      {"literal macro capture", "E094", {:expected_literal_capture, "{name}", 1, 2}},
      {"unknown syntax family field", "E092", {:unknown_syntax_family_field, :Expr, :field, 1, 2}},
      {"missing syntax family field", "E092", {:missing_syntax_family_field, :Expr, :field, 1, 2}},
      {"unknown macro obligation capture", "E092", {:unknown_macro_obligation_capture, :capture, 1, 2}},
      {"graded let requires variable", "E093", {:graded_let_requires_variable, :linear, 1, 2}},
      {"unknown grade", "E093", {:unknown_grade, :future, 1, 2}},
      {"grade requires type", "E093", {:grade_requires_type, :value, :linear, 1, 2}},
      {"reserved unit type", "E092", {:unit_type_reserved, "ms", 1, 1}},
      {"duplicate index", "E105", {:duplicate_index, :n}},
      {"multi-with proof", "E093", {:with_multi_proof_unsupported, "proof", []}},
      {"multi-with rematch", "E093", {:with_multi_rematch_unsupported, "rematch", []}},
      {"multi-with arity", "E093", {:with_multi_arity_mismatch, "arity", []}},
      {"multi-with no arms", "E093", {:with_multi_no_arms, "arms", []}},
      {"multi-with inconsistent pattern", "E093", {:with_multi_inconsistent_pattern, "patterns", []}},
      {"duplicate syntax family field", "E092", {:duplicate_syntax_family_field, :field, 1, 2}},
      {"non-associative operator", "E094", {:non_associative, :==, :chained_with, :==, 1, 2}},
      {"ambiguous precedence", "E094", {:ambiguous_precedence, :left, :right, 1, 2}}
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
          assert_no_raw_diagnostic_leaks(plain, label)

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
      assert_no_raw_diagnostic_leaks(Renderer.plain(diagnostic), label)

      assert Cure.Compiler.Errors.format_with_source(reason, "#{label}.cure", "fn run() -> Int = 1\n") =~
               expected_code,
             "#{label} still uses the legacy source formatter path"
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
      Operational.registry_fetch_failed(:timeout),
      Operational.registry_hash_mismatch("Demo@1.0.0"),
      Operational.registry_package_not_found("Demo@1.0.0"),
      Operational.package_version_conflict("Demo", [">= 1.0", "< 0.9"]),
      Operational.undocumented_public_function("demo.cure", 3),
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
             ~w[E095 E096 E097 E098 W001 W000 E068 E070 E065 E066 E067 E069 E041 E042 E038 E039 E040 E030 E008 W002 E099 E100 E101]

    registered_codes = Cure.Diagnostic.Registry.reachable() |> Enum.map(& &1.code) |> MapSet.new()
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

  defp assert_no_raw_diagnostic_leaks(plain, label) do
    assert is_binary(plain), "#{label} did not produce plain diagnostic text"
    refute plain =~ "{:"
    refute plain =~ "%{"
    refute plain =~ "Cure.Core."
    refute plain =~ "** ("
    refute plain =~ "lib/cure/"
    refute plain =~ "#Function<"
  end
end
