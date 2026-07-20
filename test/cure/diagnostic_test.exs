defmodule Cure.DiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Adapter, Label, ProvenanceFrame, Renderer, SourceRegistry, Suggestion, TextEdit}

  setup do
    source = "mod Demo\n  fn answer() -> Int = unknowñ\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:demo, source, "src/demo.cure")
    start = :binary.match(source, "unknowñ") |> elem(0)
    {:ok, span} = SourceRegistry.span(registry, :demo, start, start + byte_size("unknowñ"))
    %{registry: registry, span: span}
  end

  test "source spans retain byte offsets and Unicode display columns", %{span: span} do
    assert span.start_line == 2
    assert span.start_column == 24
    assert span.end_column == 31
    assert span.end_byte - span.start_byte == 8
  end

  test "all renderers consume the same structured diagnostic", %{registry: registry, span: span} do
    replacement = %TextEdit{span: span, replacement: "known"}

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :unknown_value,
        severity: :error,
        title: "Unknown value",
        message: "`unknowñ` is not available in this scope.",
        primary: %Label{span: span, style: :primary, message: "not found"},
        notes: ["names are namespace-sensitive"],
        suggestions: [
          %Suggestion{message: "replace it with `known`", applicability: :maybe_incorrect, edits: [replacement]}
        ],
        provenance: [%ProvenanceFrame{kind: :macro_expansion, name: "actor Worker"}],
        payload: %{namespace: :value, name: "unknowñ"}
      )

    plain = Renderer.plain(diagnostic, registry)
    terminal = Renderer.terminal(diagnostic, registry, color: true)
    machine = Renderer.to_map(diagnostic)
    lsp = Renderer.lsp(diagnostic, registry)
    host = Renderer.code_diagnostic(diagnostic)
    mix = Renderer.mix_diagnostic(diagnostic)

    assert plain =~ "-- UNKNOWN VALUE [E101]"
    assert terminal =~ IO.ANSI.cyan() <> "-- UNKNOWN VALUE [E101]"
    assert plain =~ "2 |   fn answer() -> Int = unknowñ"
    assert plain =~ "^^^^^^^ not found"
    assert terminal =~ IO.ANSI.red() <> "^^^^^^^" <> IO.ANSI.reset()
    assert plain =~ "expansion: actor Worker"
    assert machine["code"] == lsp["code"]
    assert machine["primary"]["span"]["start_byte"] == span.start_byte
    assert lsp["range"]["start"] == %{"line" => 1, "character" => 23}
    assert Jason.decode!(Renderer.json(diagnostic))["payload"]["name"] == "unknowñ"
    assert host.details == diagnostic
    assert host.position == {2, 24}
    assert mix.compiler_name == "Cure"
    assert {:ok, ^diagnostic} = Renderer.from_host_diagnostic(mix)
  end

  test "parser diagnostics underline the full unexpected token" do
    source = "mod Demo\n  fn run(] -> Int = 1\n"
    error = {:parse_error, [{:expected, :rparen, :got, :arrow, 2, 12}]}
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert diagnostic.primary.span.end_column - diagnostic.primary.span.start_column == 2
    assert Renderer.plain(diagnostic, registry) =~ "^^ this syntax does not fit here"
    assert Renderer.plain(diagnostic, registry) =~ "'->' cannot appear"
    assert Renderer.plain(diagnostic, registry) =~ "starts with ')'"
    refute Renderer.plain(diagnostic, registry) =~ "'arrow'"
    refute Renderer.plain(diagnostic, registry) =~ "'rparen'"

    assert Renderer.terminal(diagnostic, registry, color: true) =~
             IO.ANSI.red() <> "^^" <> IO.ANSI.reset()
  end

  test "parser diagnostics quote binary token spellings with single quotes" do
    error = {:parse_error, [{:expected, :rparen, :got, "->", 2, 12}]}
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", "fn f( -> Int = 1\n")

    assert Renderer.plain(diagnostic, registry) =~ "'->' cannot appear"
    refute Renderer.plain(diagnostic, registry) =~ "\"->\""
  end

  test "parser diagnostic widths come from lexer spans rather than a token-width table" do
    source = "mod Demo\n  fn run(x) => Int = x\n"
    error = {:parse_error, [{:expected, :arrow, :got, :fat_arrow, 2, 13}]}
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert diagnostic.primary.span.end_byte - diagnostic.primary.span.start_byte == 2
    assert binary_part(source, diagnostic.primary.span.start_byte, 2) == "=>"
    assert Renderer.plain(diagnostic, registry) =~ "^^ this syntax does not fit here"
  end

  test "lexer failures explain authored syntax without exposing raw tuples" do
    source = "mod Demo\n\tfn run() = 1\n"
    error = {:lex_error, {:tab_not_allowed, 2, 1}}
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert diagnostic.code == "E094"
    assert diagnostic.title == "Tabs are not valid indentation"
    assert Renderer.plain(diagnostic, registry) =~ "indentation uses spaces"
    refute Renderer.plain(diagnostic, registry) =~ "{:tab_not_allowed"
  end

  test "parser producer tuples retain trailing source coordinates" do
    source = "mod Demo\n  x\n"

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:unknown_syntax_family_field, :Expr, :field, 2, 3},
        "demo.cure",
        source
      )

    assert diagnostic.code == "E092"
    assert diagnostic.primary.span.start_line == 2
    assert diagnostic.primary.span.start_column == 3
    assert Renderer.plain(diagnostic, registry) =~ "2 |   x"
  end

  test "operational failure tuples use the declared registry converter" do
    entry = Cure.Diagnostic.Registry.fetch!("E095")
    diagnostic = apply(entry.converter, entry.converter_function, [{:file_read_error, "demo.cure", :enoent}, []])

    assert diagnostic.code == "E095"
    assert Diagnostic.message(diagnostic) == "Cannot read `demo.cure`: no such file or directory"
  end

  test "kernel, module, extern, and macro rejection families have structured verdicts" do
    cases = [
      {{:hole_in_inference_position, "h"}, "E093"},
      {{:ctor_requires_checking_mode, "Nat"}, "E093"},
      {{:bounded_bound_not_concrete, {:literal, 10}}, "E093"},
      {{:cyclic_typealiases, ["A", "B"]}, "E105"},
      {{:module_identity_missing, "demo.cure"}, "E095"},
      {{:module_identity_mismatch, "Demo", "Other", "demo.cure"}, "E105"},
      {{:char_literal_needs_bounded, 97}, "E093"},
      {{:char_literal_out_of_range, 0x110000}, "E093"},
      {{:extern_returns_union, "foreign", {:union, []}}, "E093"},
      {{:extern_union_indistinct, "foreign", :duplicate}, "E093"},
      {{:cannot_infer_dependent_match, :branch}, "E093"},
      {{:bidirectional_erased_field, "Ctor"}, "E093"},
      {{:label_mismatch, :label, [:declared], [:written]}, "E093"},
      {{:forced_pattern_not_in_pattern, :name}, "E093"},
      {{:named_implicit_not_in_pattern, :implicit}, "E093"},
      {{:unsolved_parameters, :Ctor}, "E093"},
      {{:cannot_emit, :invalid_form}, "E101"},
      {{:inconsistent_head_kind, :Thing}, "E105"},
      {{:unbound_var, :missing}, "E091"},
      {{:unknown_family, :Missing}, "E091"},
      {{:unknown_ctor, :Missing}, "E091"},
      {{:foreign_ctor, :Missing}, "E091"},
      {{:primitive_missing_builtin, :Int}, "E092"},
      {{:unknown_primitive_tag, :future_primitive}, "E092"},
      {{:primitive_floor_mismatch, :Int, :node, :floor}, "E092"},
      {{:unsupported_declaration, :future_declaration}, "E092"},
      {{:invalid_syntax_node, :attrs}, "E092"},
      {{:raw_syntax_in_expansion, [:root]}, "E092"},
      {{:invalid_macro_rules, :rules}, "E092"},
      {{:invalid_packet_name, :packet}, "E092"},
      {{:duplicate_packet_field, :field}, "E092"},
      {{:invalid_driver_register, :register}, "E092"},
      {{:module_rule_not_fully_consumed, :rule}, "E092"},
      {{:ambiguous_macro_extension, [:actor]}, "E092"},
      {{:invalid_macro_diagnostics, :diagnostics}, "E092"},
      {{:left_recursive_parse_production, [:expr]}, "E092"},
      {{:protocol_role_count, 3}, "E092"},
      {{:reserved_syntax_field, "context", ["mk"]}, "E092"},
      {{:invalid_macro_segment, :segment}, "E092"},
      {{:unknown_reducer_constructor, [:Ctor]}, "E092"},
      {{:incomplete_reducer, [:Ctor]}, "E092"},
      {{:reducer_arity, :Ctor, 1, 2}, "E092"},
      {{:generated_hole_not_well_typed, :term}, "E092"},
      {{:example_use_site_not_fully_consumed, [], :ast}, "E092"},
      {{:closed_category_extension, [:expression]}, "E092"},
      {{:duplicate_unit, "ms"}, "E092"},
      {{:invalid_unit, "ms"}, "E092"},
      {{:unknown_unit, "ms"}, "E092"},
      {{:invalid_board_name, 42}, "E092"},
      {:invalid_board_pins, "E092"},
      {:invalid_board_capabilities, "E092"},
      {:invalid_board_buses, "E092"},
      {:invalid_board_flash, "E092"},
      {:flash_offset_out_of_bounds, "E092"},
      {{:unsupported_hole_arity, 3}, "E092"},
      {{:bad_grade, :not_a_grade}, "E100"},
      {{:unknown_symbol, "not_loaded"}, "E100"},
      {{:ill_formed_term, {:not_core, 1}}, "E100"},
      {:bounded_family_unregistered, "E093"},
      {:absurd_in_reachable_position, "E093"},
      {:opaque_not_eliminable, "E093"},
      {:case_scrutinee_not_data, "E093"},
      {:not_total, "E093"},
      {:not_a_function, "E093"},
      {:coverage, "E093"},
      {:branch_arity, "E093"},
      {:branch_type, "E093"},
      {:index_arity, "E093"},
      {:applied_non_function, "E093"},
      {:rewrite_requires_expected_type, "E093"},
      {:rewrite_proof_not_equality, "E093"},
      {:match_scrutinee_not_data, "E093"},
      {:with_mixed_rematch_arms, "E093"},
      {:with_scrutinee_not_data, "E093"},
      {:too_few_arguments, "E093"},
      {:too_many_arguments, "E093"},
      {:nonvariable_scrutinee, "E093"},
      {:no_compatible_macro_input, "E092"},
      {:normalization_fuel_exhausted, "E092"},
      {:invalid_parse_production, "E092"},
      {:duplicate_parse_production, "E092"},
      {:invalid_macro_diagnostics, "E092"},
      {:invalid_macro_diagnostic, "E092"},
      {:invalid_syntax_attr, "E092"},
      {:invalid_syntax_list, "E092"},
      {:invalid_syntax_string, "E092"},
      {:invalid_syntax_literal, "E092"},
      {:invalid_syntax_pair, "E092"},
      {:invalid_check_property, "E092"},
      {:duplicate_check_property, "E092"},
      {:invalid_protocol_role, "E092"},
      {:duplicate_protocol_role, "E092"},
      {:duplicate_reducer_constructor, "E092"},
      {:not_a_nat, "E092"},
      {:invalid_lift_module_ast, "E092"},
      {:invalid_lift_callback, "E092"},
      {:invalid_lift_declaration, "E092"},
      {:invalid_lift_import, "E092"},
      {:invalid_driver_register, "E092"},
      {:duplicate_driver_register, "E092"},
      {:overlapping_driver_register, "E092"},
      {:module_rule_not_fully_consumed, "E092"},
      {:not_a_module_rule, "E092"},
      {:expander_without_accepts, "E092"},
      {:accepts_without_syntax_family, "E092"},
      {:accepts_without_expander, "E092"},
      {:multiple_accepts_declarations, "E092"},
      {:multiple_expands_declarations, "E092"},
      {{:expected_literal_capture, "{name}", 1, 2}, "E094"},
      {{:unknown_syntax_family_field, :Expr, :field, 1, 2}, "E092"},
      {{:missing_syntax_family_field, :Expr, :field, 1, 2}, "E092"},
      {{:unknown_macro_obligation_capture, :capture, 1, 2}, "E092"},
      {{:graded_let_requires_variable, :linear, 1, 2}, "E093"},
      {{:unknown_grade, :future, 1, 2}, "E093"},
      {{:grade_requires_type, :value, :linear, 1, 2}, "E093"},
      {{:unit_type_reserved, "ms"}, "E092"},
      {{:unit_type_reserved, "ms", 1, 2}, "E092"},
      {{:duplicate_index, :n}, "E105"},
      {{:with_multi_proof_unsupported, "proof"}, "E093"},
      {{:with_multi_rematch_unsupported, "rematch"}, "E093"},
      {{:with_multi_arity_mismatch, "arity"}, "E093"},
      {{:with_multi_proof_unsupported, "proof", []}, "E093"},
      {{:with_multi_rematch_unsupported, "rematch", []}, "E093"},
      {{:with_multi_arity_mismatch, "arity", []}, "E093"},
      {{:with_multi_no_arms, "arms", []}, "E093"},
      {{:with_multi_inconsistent_pattern, "patterns", []}, "E093"},
      {{:duplicate_syntax_family_field, :field, 1, 2}, "E092"},
      {{:non_associative, :==, :chained_with, :==, 1, 2}, "E094"},
      {{:ambiguous_precedence, :left, :right, 1, 2}, "E094"}
    ]

    for {reason, code} <- cases do
      diagnostic = Adapter.from_error(reason)
      assert diagnostic.code == code, "#{inspect(reason)} rendered as #{diagnostic.code}"
      assert is_binary(Diagnostic.message(diagnostic))
    end
  end

  test "literal macro captures retain a contextual syntax diagnostic" do
    diagnostic = Adapter.from_error({:expected_literal_capture, "{name}", 1, 2})

    assert diagnostic.code == "E094"
    assert diagnostic.title == "Macro literal capture is invalid"
    assert Diagnostic.message(diagnostic) =~ "literal shape"
    refute Diagnostic.message(diagnostic) =~ "{:expected_literal_capture"
  end

  test "unique missing lexer delimiters provide an insertion edit" do
    source = "\"not closed"
    error = {:lex_error, {:unterminated_string, 1, 1}}
    {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert [%Suggestion{applicability: :machine_applicable, edits: [%TextEdit{replacement: "\""}]}] =
             diagnostic.suggestions
  end

  test "Core artifact failures keep native details out of prose but in payload" do
    diagnostic = Adapter.from_error({:unknown_symbol, "not_loaded"})

    assert diagnostic.code == "E100"
    assert diagnostic.payload == %{kind: :unknown_symbol, symbol: "not_loaded"}
    refute Diagnostic.message(diagnostic) =~ "not_loaded"
    refute Diagnostic.message(diagnostic) =~ "{:unknown_symbol"
  end

  test "LSP positions count UTF-16 code units rather than Unicode scalars" do
    registry = SourceRegistry.new() |> SourceRegistry.register(:astral, "a😀b", "astral.cure")
    {:ok, span} = SourceRegistry.span(registry, :astral, 5, 6)
    label = %Label{span: span, style: :primary}

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :unknown_value,
        severity: :error,
        title: "Unknown",
        message: "missing",
        primary: label
      )

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 3},
             "end" => %{"line" => 0, "character" => 4}
           }

    assert Renderer.lsp(diagnostic, registry, :utf8)["range"]["start"]["character"] == 5
    assert Renderer.lsp(diagnostic, registry, :utf32)["range"]["start"]["character"] == 2
  end

  test "one-based source coordinates normalize to canonical byte spans" do
    registry = SourceRegistry.new() |> SourceRegistry.register(:source, "αβ\nvalue\n", "unicode.cure")
    assert {:ok, span} = SourceRegistry.span_at(registry, :source, 2, 2, 3)
    assert {span.start_byte, span.end_byte} == {6, 9}
    assert {span.start_line, span.start_column, span.end_column} == {2, 2, 5}
  end

  test "stable category extraction supports diagnostics and legacy shapes" do
    diagnostic =
      Diagnostic.new(code: "E101", key: :unknown_value, severity: :error, title: "Unknown", message: "missing")

    assert Diagnostic.key(diagnostic) == :unknown_value
    assert Diagnostic.key({:error, {:unknown_global, :missing}}) == :unknown_global
    assert Diagnostic.code({:extern_untyped_head, "needs a type (E056)", line: 2}) == "E056"
  end

  test "unknown-name adapter retains namespace, offender, candidates, and source", %{registry: registry, span: span} do
    diagnostic =
      Adapter.from_error({:unknown_constructor, :Nothng},
        span: span,
        candidates: [:Nothing, :Something],
        checking: :decode
      )

    assert diagnostic.code == "E091"
    assert diagnostic.key == :unknown_name
    assert diagnostic.payload.namespace == :constructor
    assert diagnostic.payload.name == "Nothng"
    assert diagnostic.payload.checking == :decode
    assert Renderer.plain(diagnostic, registry) =~ "`Nothng` was not found"
    assert hd(diagnostic.suggestions).message =~ "`Nothing`"
  end

  test "name candidates rank usable namespace and arity matches before spelling" do
    diagnostic =
      Adapter.unknown_name(:value, "map",
        arity: 2,
        candidates: [
          %{name: "map", namespace: :type, arity: 2, visibility: :public},
          %{name: "map", namespace: :value, arity: 2, visibility: :private},
          %{name: "mop", namespace: :value, arity: 1, visibility: :public},
          %{name: "map_values", namespace: :value, arity: 2, visibility: :private},
          %{name: "map_values", namespace: :value, arity: 2, visibility: :public}
        ]
      )

    assert diagnostic.payload.candidates == ["map_values", "mop", "map"]
    assert hd(diagnostic.payload.candidate_details).visibility == :public
    assert hd(diagnostic.payload.candidate_details).arity == 2
  end

  test "name ranking is case-insensitive and recognizes adjacent transpositions" do
    diagnostic =
      Adapter.unknown_name(:value, "Nmae",
        candidates: [%{name: "Name", namespace: :value, visibility: :public, imported: true}]
      )

    assert diagnostic.payload.candidates == ["Name"]
  end

  test "conversion failures present Cure types and retain Core payloads", %{registry: registry, span: span} do
    actual = {:data, :"Std.Bool#Bool", [], []}
    expected = {:data, :"Std.Int#Int", [], []}
    diagnostic = Adapter.from_error({:conversion_failure, actual, expected}, span: span)

    assert diagnostic.code == "E093"
    assert Diagnostic.message(diagnostic) == "Expected: Int\nFound:    Bool"
    assert diagnostic.payload.expected_surface == "Int"
    assert diagnostic.payload.actual_surface == "Bool"
    assert diagnostic.payload.expected_core == inspect(expected)
    assert Renderer.plain(diagnostic, registry) =~ "this expression has the wrong type"
  end

  test "type comparisons highlight only a mismatch below a shared type constructor", %{
    registry: registry,
    span: span
  } do
    nat = {:data, :"Std.Nat#Nat", [], []}
    zero = {:ctor, :"Std.Nat#Z", []}
    successor = {:ctor, :"Std.Nat#S", [zero]}

    expected = {:data, :"Std.Equivalent#Equivalent", [nat, zero, successor], []}
    actual = {:data, :"Std.Equivalent#Equivalent", [nat, zero, zero], []}

    diagnostic = Adapter.from_error({:conversion_failure, actual, expected}, span: span)
    terminal = Renderer.terminal(diagnostic, registry, color: :always)

    assert Diagnostic.message(diagnostic) ==
             "Expected: Equivalent(Nat, Z, S(Z))\nFound:    Equivalent(Nat, Z, Z)"

    refute terminal =~ IO.ANSI.green() <> "Equivalent"
    refute terminal =~ IO.ANSI.red() <> "Equivalent"
    assert terminal =~ IO.ANSI.green() <> "S(Z)"
    assert terminal =~ IO.ANSI.red() <> "Z"
  end

  test "unrelated type roots remain uncoloured", %{registry: registry, span: span} do
    actual = {:data, :"Std.Bool#Bool", [], []}
    expected = {:data, :"Std.Int#Int", [], []}

    terminal =
      {:conversion_failure, actual, expected}
      |> Adapter.from_error(span: span)
      |> Renderer.terminal(registry, color: :always)

    refute terminal =~ IO.ANSI.green() <> "Int"
    refute terminal =~ IO.ANSI.red() <> "Bool"
  end

  test "type mismatch prose follows its expectation origin", %{registry: registry, span: span} do
    annotation_origin = %Cure.Diagnostic.ExpectationOrigin{kind: :annotation, span: span}
    condition_origin = %Cure.Diagnostic.ExpectationOrigin{kind: :condition}

    annotation =
      Adapter.from_error(%Cure.Diagnostic.TypeProblem{
        kind: :type_mismatch,
        actual: "String",
        expected: "Int",
        origin: annotation_origin,
        span: span
      })

    condition =
      Adapter.from_error(%Cure.Diagnostic.TypeProblem{
        kind: :type_mismatch,
        actual: "Int",
        expected: "Bool",
        origin: condition_origin,
        span: span
      })

    application =
      Adapter.from_error(%Cure.Diagnostic.TypeProblem{
        kind: :type_mismatch,
        actual: "String",
        expected: "Int",
        origin: %Cure.Diagnostic.ExpectationOrigin{kind: :application},
        span: span
      })

    overload =
      Adapter.from_error(%Cure.Diagnostic.TypeProblem{
        kind: :type_mismatch,
        actual: "String",
        expected: "Int",
        origin: %Cure.Diagnostic.ExpectationOrigin{kind: :overload, owner: "map"},
        span: span
      })

    assert annotation.title == "Annotation does not match"
    assert Renderer.plain(annotation, registry) =~ "type written in its annotation"
    assert Renderer.plain(annotation, registry) =~ "Expected: Int\nFound:    String"
    assert condition.title == "Condition is not boolean"
    assert application.title == "Application has the wrong type"
    assert Renderer.plain(application, registry) =~ "application has the wrong type"
    assert overload.title == "No matching overload"
    assert Renderer.plain(overload, registry) =~ "overloaded call `map`"
    assert Renderer.plain(condition, registry) =~ "condition must produce `Bool`"
    condition_terminal = Renderer.terminal(condition, registry, color: :always)
    refute condition_terminal =~ IO.ANSI.green() <> "Bool"
    refute condition_terminal =~ IO.ANSI.red() <> "Int"
    assert condition.payload.actual_core == inspect("Int")
  end

  test "all contextual type origins retain specialized user-facing titles", %{span: span} do
    origins = [
      {:call_result, "Call result has the wrong type"},
      {:element, "Collection element has the wrong type"},
      {:record, "Record has the wrong type"},
      {:record_field, "Record field has the wrong type"},
      {:record_update, "Record update has the wrong type"},
      {:pattern, "Pattern has the wrong type"},
      {:constructor_argument, "Constructor argument has the wrong type"},
      {:implicit, "Implicit argument has the wrong type"},
      {:ffi, "FFI boundary has the wrong type"},
      {:actor, "Actor message has the wrong type"},
      {:fsm, "FSM transition has the wrong type"},
      {:supervisor, "Supervisor value has the wrong type"}
    ]

    for {kind, title} <- origins do
      diagnostic =
        Adapter.from_error(%Cure.Diagnostic.TypeProblem{
          kind: :type_mismatch,
          actual: "String",
          expected: "Int",
          origin: %Cure.Diagnostic.ExpectationOrigin{kind: kind},
          span: span
        })

      assert diagnostic.title == title
      assert diagnostic.title != "Type mismatch"
    end
  end

  test "source checking context upgrades kernel conversion failures", %{registry: registry, span: span} do
    diagnostic =
      Adapter.from_error(
        {:source_context, {:conversion_failure, {:bool_type}, {:int_type}},
         %{
           checking: :answer,
           span: span,
           expression_category: :literal,
           expectation_origin: :annotation
         }}
      )

    assert diagnostic.title == "Annotation does not match"
    assert diagnostic.payload.origin.kind == :annotation
    assert diagnostic.payload.origin.owner == :answer
    assert diagnostic.payload.expression_category == :literal
    assert diagnostic.payload.debug.cause == {:conversion_failure, {:bool_type}, {:int_type}}
    assert Renderer.plain(diagnostic, registry) =~ "type written in its annotation"
  end

  test "plain rendering includes cross-file secondary labels", %{registry: registry, span: span} do
    registry = SourceRegistry.register(registry, :definition, "type Token = Token\n", "src/token.cure")
    {:ok, definition_span} = SourceRegistry.span(registry, :definition, 5, 10)

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :type_mismatch,
        severity: :error,
        title: "Type mismatch",
        message: "The values have different types.",
        primary: %Label{span: span, style: :primary, message: "used here"},
        secondary: [%Label{span: definition_span, style: :secondary, message: "defined here"}]
      )

    rendered = Renderer.plain(diagnostic, registry)
    assert rendered =~ "at src/token.cure:1:6"
    assert rendered =~ "1 | type Token = Token"
    assert rendered =~ "----- defined here"
  end

  test "carets align after tabs and multiline labels underline every covered line" do
    source = "head\n\tbody\nlast"
    registry = SourceRegistry.new() |> SourceRegistry.register(:multi, source, "multi.cure")
    {:ok, span} = SourceRegistry.span(registry, :multi, 2, 13)

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :type_mismatch,
        severity: :error,
        title: "Type mismatch",
        message: "covered expression failed",
        primary: %Label{span: span, style: :primary, message: "whole expression"}
      )

    rendered = Renderer.plain(diagnostic, registry)
    assert rendered =~ "1 | head\n  >   ^^"
    assert rendered =~ "2 |     body\n  > ^^^^^^^^"
    assert rendered =~ "3 | last\n  > ^^ whole expression"
  end

  test "zero-width insertion spans still render one caret" do
    registry = SourceRegistry.new() |> SourceRegistry.register(:insert, "abc", "insert.cure")
    {:ok, span} = SourceRegistry.span(registry, :insert, 1, 1)

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :missing_token,
        severity: :error,
        title: "Missing token",
        message: "insert a token",
        primary: %Label{span: span, style: :primary, message: "insert here"}
      )

    assert Renderer.plain(diagnostic, registry) =~ "1 | abc\n  |  ^ insert here"
  end

  test "machine-applicable structured edits become LSP quick fixes", %{registry: registry, span: span} do
    diagnostic =
      Diagnostic.new(
        code: "E091",
        key: :unknown_name,
        severity: :error,
        title: "Unknown value",
        message: "The value is not in scope.",
        primary: %Label{span: span, style: :primary},
        suggestions: [
          %Suggestion{
            message: "Replace it with `known`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: "known"}]
          }
        ]
      )

    lsp = Renderer.lsp(diagnostic, registry)
    assert [action] = Cure.LSP.Server.compute_code_actions("file:///fallback.cure", [lsp])
    assert action["title"] == "Replace it with `known`"

    assert [{uri, edits}] = Map.to_list(get_in(action, ["edit", "changes"]))
    assert String.ends_with?(uri, "/src/demo.cure")

    assert edits == [
             %{
               "range" => %{
                 "start" => %{"line" => 1, "character" => 23},
                 "end" => %{"line" => 1, "character" => 30}
               },
               "newText" => "known"
             }
           ]
  end

  test "lifted module failures are reported at the public macro boundary" do
    diagnostic =
      Adapter.from_error(
        {:lift_module_error,
         %{
           module: "Cure.Actor.Worker",
           behaviour: :GenServer,
           source_provenance: %{file: "worker.cure", line: 3, col: 1, macro: "actor"},
           expansion_provenance: [%{keyword: "actor", line: 3, col: 1}],
           cause: {:unknown_global, :MissingMessage}
         }}
      )

    assert diagnostic.code == "E092"
    assert diagnostic.title == "Actor expansion failed"
    assert Diagnostic.message(diagnostic) =~ "`MissingMessage` is not available"
    assert diagnostic.payload.cause.code == "E091"
    assert diagnostic.payload.cause.payload.name == "MissingMessage"
    refute Diagnostic.message(diagnostic) =~ "{:unknown_global"
    assert Renderer.plain(diagnostic) =~ "edit the `actor`"
    assert Renderer.plain(diagnostic) =~ "declaration instead"

    machine = Jason.decode!(Renderer.json(diagnostic))
    assert machine["payload"]["cause"]["code"] == "E091"
    assert machine["body"]["kind"] == "paragraph"
  end

  test "compiler presentation attaches a real caret to an authored macro failure" do
    source = "mod Demo\n  actor Worker\n"

    error =
      {:lift_module_error,
       %{
         module: "Cure.Actor.Worker",
         behaviour: :GenServer,
         source_provenance: %{file: "worker.cure", line: 2, col: 3, macro: "actor"},
         expansion_provenance: [%{keyword: "actor", line: 2, col: 3}],
         cause: {:unknown_global, :MissingMessage}
       }}

    rendered = Cure.Compiler.Errors.format_with_source(error, "worker.cure", source)
    assert rendered =~ "2 |   actor Worker"
    assert rendered =~ "  ^ this `actor` declaration generated the failing module"
    refute rendered =~ "{:unknown_global"
  end

  test "invalid spans and codes are rejected", %{registry: registry} do
    assert {:error, :span_out_of_bounds} = SourceRegistry.span(registry, :demo, 0, 10_000)

    assert_raise ArgumentError, fn ->
      Diagnostic.new(code: "unknown", key: :bad, severity: :error, title: "Bad", message: "bad")
    end
  end

  test "unregistered domain errors fail loudly instead of becoming generic diagnostics" do
    assert_raise Cure.Diagnostic.UnhandledError, ~r/no registered diagnostic conversion/, fn ->
      Adapter.from_error({:new_unregistered_error, :detail})
    end

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      Cure.Compiler.Errors.format_error({:new_unregistered_error, :detail}, "source.cure")
    end
  end

  test "operational failures use stable diagnostic codes" do
    diagnostic = Cure.Diagnostic.Operational.file_read("Cure.toml", :enoent)
    assert diagnostic.code == "E095"
    assert diagnostic.key == :file_read
    assert diagnostic.payload.path == "Cure.toml"
  end

  test "migration warnings render as rich diagnostics" do
    warning =
      Cure.Diagnostic.Operational.migration_warning(%{
        rule: :legacy,
        file: "demo.cure",
        line: 3,
        message: "use the modern form"
      })

    assert warning.severity == :warning
    assert warning.code == "W001"
    assert Cure.Diagnostic.Renderer.plain(warning) =~ "W001"
    assert Cure.Diagnostic.Renderer.plain(warning) =~ "use the modern form"
  end

  test "specialized operational warnings retain stable codes" do
    assert Cure.Diagnostic.Operational.export_unmappable("dependent").code == "E068"
    assert Cure.Diagnostic.Operational.snap_missing("missing.cure").code == "E070"
    assert Cure.Diagnostic.Operational.configuration_warning("bad setting").code == "W002"
  end

  test "task usage and artifact failures are structured" do
    assert Cure.Diagnostic.Operational.usage("bad args").code == "E099"
    assert Cure.Diagnostic.Operational.artifact_error("missing").code == "E100"
  end

  test "codegen-wrapped unknown globals remain structured" do
    rendered = Cure.Compiler.Errors.format_error({:codegen_error, {:unknown_global, :Missing}}, "demo.cure")
    assert rendered =~ "E091"
    refute rendered =~ "{:unknown_global"
  end

  test "payload-bearing unknown names retain resolution context" do
    diagnostic =
      Adapter.from_error(
        {:unknown_name, %{namespace: :type, name: :Missing, candidates: [:Maybe], arity: 1, checking: :Demo}}
      )

    assert diagnostic.code == "E091"
    assert diagnostic.payload.namespace == :type
    assert diagnostic.payload.candidates == ["Maybe"]
    assert diagnostic.payload.arity == 1
    assert diagnostic.payload.checking == :Demo
  end

  test "structured body is authoritative and machine output retains its semantics" do
    diagnostic =
      Diagnostic.new(
        code: "E093",
        key: :conversion_failure,
        severity: :error,
        title: "Type mismatch",
        body:
          Cure.Diagnostic.Doc.paragraph([
            "Expected",
            Cure.Diagnostic.Doc.emphasis(:expected, "Int"),
            "but found",
            Cure.Diagnostic.Doc.emphasis(:observed, "Bool")
          ])
      )

    refute Map.has_key?(diagnostic, :message)
    assert Diagnostic.message(diagnostic) == "Expected Int but found Bool"
    assert Renderer.to_map(diagnostic)["body"]["kind"] == "paragraph"
  end

  test "renderer wraps at an explicit width and normalizes the banner path", %{registry: registry, span: span} do
    diagnostic =
      Diagnostic.new(
        code: "E091",
        key: :unknown_name,
        severity: :error,
        title: "Unknown value",
        message: "This deliberately long explanation wraps at the requested terminal width.",
        primary: %Label{span: span, style: :primary}
      )

    rendered = Renderer.plain(diagnostic, registry, width: 38, project_root: File.cwd!())
    [banner | _] = String.split(rendered, "\n")

    assert banner =~ "[E091]"
    assert String.ends_with?(banner, " src/demo.cure")
    assert rendered =~ "This deliberately long explanation\nwraps at the requested terminal width."
  end

  test "auto color emits no ANSI when output is redirected" do
    diagnostic =
      Diagnostic.new(code: "E095", key: :file_read, severity: :error, title: "File error", message: "missing")

    {:ok, output} = StringIO.open("")

    refute Renderer.terminal(diagnostic, nil, color: :auto, output_device: output) =~ "\e["
    assert Renderer.terminal(diagnostic, nil, color: :always) =~ IO.ANSI.cyan()
    refute Renderer.terminal(diagnostic, nil, color: :never) =~ "\e["
  end
end
