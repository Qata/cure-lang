defmodule Cure.Diagnostic.Adapter.TypeTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, ExpectationOrigin, Renderer, SourceRegistry, TypeProblem}
  alias Cure.Diagnostic.Adapter.Type, as: TypeAdapter

  test "the canonical type family preserves contextual prose, both source labels, and exact output" do
    source = "fn run() -> Int = true\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:type_test, source, "type.cure")
    {:ok, expected_span} = SourceRegistry.span(registry, :type_test, 12, 15)
    {:ok, actual_span} = SourceRegistry.span(registry, :type_test, 18, 22)

    problem = %TypeProblem{
      kind: :type_mismatch,
      actual: "Bool",
      expected: "Int",
      origin: %ExpectationOrigin{kind: :annotation, span: expected_span},
      expression: :literal,
      span: actual_span
    }

    direct = TypeAdapter.from_error(problem)
    assert Adapter.from_error(problem) == direct

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- ANNOTATION DOES NOT MATCH [E093] ---------------------------------- type.cure

             This expression does not match the type written in its annotation.

             Expected: Int
             Found:    Bool

             at type.cure:1:19
             1 | fn run() -> Int = true
               |             ---   ^^^^ the expectation comes from here; this expression has the wrong type
             """
             |> String.trim_trailing()
  end

  test "Core and constraints remain debug-only at the family boundary" do
    problem = %TypeProblem{
      kind: :conversion_failure,
      actual: {:data, :Actual, [], []},
      expected: {:data, :Expected, [], []},
      origin: %ExpectationOrigin{kind: :annotation},
      debug: %{constraints: [{:cannot_unify, :actual, :expected}]}
    }

    regular = TypeAdapter.from_error(problem)
    debug = TypeAdapter.from_error(problem, debug: true)

    refute Map.has_key?(regular.payload, :debug)
    refute Renderer.json(regular) =~ "cannot_unify"
    assert debug.payload.debug.details == problem.debug
    assert Renderer.json(debug) =~ "cannot_unify"
  end

  test "legacy contextual failures expose their retained repair as a source-tagged hint" do
    source = "value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:legacy_type, source, "type_context.cure")
    {:ok, span} = SourceRegistry.span(registry, :legacy_type, 0, 5)

    diagnostic = Adapter.from_error(:not_a_function, span: span)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             """
             -- APPLICATION TARGET IS NOT CALLABLE [E093] ----------------- type_context.cure

             This value is used as a function, but its type is not callable.

             at type_context.cure:1:1
             1 | value
               | ^^^^^ apply a function or constructor value

             Hint: Apply a function or constructor value
             """
             |> String.trim_trailing()
  end

  test "raw kernel conversion failures normalize through the type family" do
    raw = {:conversion_failure, {:data, :Bool, [], []}, {:data, :Int, [], []}}
    assert TypeAdapter.from_error(raw) == Adapter.from_error(raw)

    contextual =
      {:source_context, raw,
       %{
         expectation_origin: :call_argument,
         checking: :consume,
         argument_index: 0,
         expression_category: :call
       }}

    direct = TypeAdapter.from_error(contextual)
    assert Adapter.from_error(contextual) == direct
    assert direct.code == "E093"
    assert direct.title == "Argument has the wrong type"
    assert direct.payload.origin.owner == :consume
    assert direct.payload.origin.index == 0

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      TypeAdapter.from_error({:unknown_global, :missing})
    end
  end

  test "lambda expectation failures are identical through the family and root adapter" do
    source = "fn (x) -> x end\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:lambda, source, "lambda.cure")
    {:ok, lambda_span} = SourceRegistry.span(registry, :lambda, 0, 15)
    {:ok, parameter_span} = SourceRegistry.span(registry, :lambda, 4, 5)

    error =
      {:lambda_expected_pi, %{expected: {:data, :Bool, [], []}, parameter_index: 0, parameter_span: parameter_span}}

    direct = TypeAdapter.from_error(error, span: lambda_span)
    assert Adapter.from_error(error, span: lambda_span) == direct
    assert direct.primary.span == lambda_span
    assert hd(direct.secondary).span == parameter_span

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "LAMBDA NEEDS A FUNCTION TYPE [E093]"
    assert rendered =~ "This lambda has parameter 1"
    assert rendered =~ "this parameter needs a function input type"
    assert rendered =~ "Hint: Pass this lambda to a function-valued parameter"
  end

  test "branch failures identify a singleton type outlier through the type family" do
    source = "A -> one\nB -> two\nC -> odd\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:branches, source, "branches.cure")
    {:ok, a_span} = SourceRegistry.span(registry, :branches, 0, 8)
    {:ok, b_span} = SourceRegistry.span(registry, :branches, 9, 17)
    {:ok, c_span} = SourceRegistry.span(registry, :branches, 18, 26)
    common = {:data, :Common, [], []}
    outlier = {:data, :Outlier, [], []}

    error =
      {:source_context,
       {:branch_type,
        %{
          branches: [
            %{constructor: :A, actual: common, expected: common, status: :ok},
            %{constructor: :B, actual: common, expected: common, status: :ok},
            %{constructor: :C, actual: outlier, expected: common, status: {:error, :branch_type}}
          ]
        }},
       %{
         checking: :choose,
         branch_patterns: [
           %{name: "A", span: a_span},
           %{name: "B", span: b_span},
           %{name: "C", span: c_span}
         ]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == c_span
    assert Enum.map(direct.secondary, & &1.span) == [a_span, b_span]
    assert direct.payload.failing_branch == :C

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "only the `C` branch has type `Outlier`"
    assert rendered =~ "possible outlier: this branch has the incompatible type"
    assert rendered =~ "compare this branch with the declared result"
  end

  test "operator failures preserve operator and operand regions through the type family" do
    source = "left + right\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:operator, source, "operator.cure")
    {:ok, left} = SourceRegistry.span(registry, :operator, 0, 4)
    {:ok, operator} = SourceRegistry.span(registry, :operator, 5, 6)
    {:ok, right} = SourceRegistry.span(registry, :operator, 7, 12)

    error =
      {:source_context, {:unsupported_operand_type, :+},
       %{
         operator_span: operator,
         operand_spans: [left, right],
         operand_types: [{:data, :Int, [], []}, {:data, :Bool, [], []}]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == operator
    assert Enum.map(direct.secondary, & &1.span) == [left, right]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "The `+` operator does not accept `Int` on the left and `Bool` on the right"
    assert rendered =~ "the left operand has type `Int`"
    assert rendered =~ "the right operand has type `Bool`"
    assert rendered =~ "Hint: Change the operand types"
  end

  test "instance and overload resolution failures are owned by the type family" do
    source = "call(value)\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:resolution, source, "resolution.cure")
    {:ok, span} = SourceRegistry.span(registry, :resolution, 0, 11)

    errors = [
      {:source_context, {:no_instance, :Equatable, {:rigid, 0}},
       %{span: span, checking: :same, expectation_origin: :implicit}},
      {:no_matching_overload,
       %{
         name: :map,
         arguments: [:Int],
         candidates: [%{id: "List.map", owner: "List", parameters: [:List]}]
       }},
      {:ambiguous_overload, :map, ["List", "Sequence"]}
    ]

    for error <- errors do
      direct = TypeAdapter.from_error(error, span: span)
      assert Adapter.from_error(error, span: span) == direct
      assert direct.code == "E093"
      assert direct.primary.span == span
      assert direct.suggestions != []
    end

    instance = errors |> hd() |> TypeAdapter.from_error(span: span)
    assert instance.payload.head_kind == :type_variable
    assert Renderer.plain(instance, registry, width: 80) =~ "Add a `where Equatable(...)` constraint"

    mismatch = errors |> Enum.at(1) |> TypeAdapter.from_error(span: span)
    assert Renderer.plain(mismatch, registry, width: 80) =~ "`List.map(List)`"

    ambiguity = errors |> Enum.at(2) |> TypeAdapter.from_error(span: span)

    assert Renderer.plain(ambiguity, registry, width: 80) =~
             "Hint: Choose `List.map(...)` or `Sequence.map(...)`"
  end

  test "non-callable applications label the value and stranded argument" do
    source = "value(argument)\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:application, source, "application.cure")
    {:ok, callee} = SourceRegistry.span(registry, :application, 0, 5)
    {:ok, argument} = SourceRegistry.span(registry, :application, 6, 14)

    error =
      {:source_context, {:applied_non_function, %{actual: {:data, :Int, [], []}, argument_index: 0}},
       %{callee_span: callee, argument_span: argument, callee_name: :value}}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == callee
    assert hd(direct.secondary).span == argument

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- `INT` VALUE IS NOT CALLABLE [E093] ------------------------- application.cure

             Parentheses apply a function or constructor, but this expression has type `Int`.
             It cannot accept the argument written after it.

             at application.cure:1:1
             1 | value(argument)
               | ^^^^^ -------- this expression has type `Int`, not a function type; this argument has nowhere to go

             Hint: Remove the parentheses, or replace this expression with a function or constructor
             """
             |> String.trim_trailing()
  end

  test "match inference labels every pattern that fails to identify a constructor" do
    source = "match value\n  _ -> value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:match, source, "match.cure")
    {:ok, whole} = SourceRegistry.span(registry, :match, 0, 25)
    {:ok, pattern} = SourceRegistry.span(registry, :match, 14, 15)

    error =
      {:cannot_infer_match_type,
       %{
         reason: :no_constructor_arm,
         span: whole,
         branch_spans: [pattern],
         expression_category: :pattern_match
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == whole
    assert hd(direct.secondary).span == pattern

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "MATCH RESULT NEEDS AN ANNOTATION [E093]"
    assert rendered =~ "this pattern does not identify a constructor"
    assert rendered =~ "Hint: Add a result annotation"
  end

  test "non-data match and with failures retain scrutinee and branch regions" do
    source = "with value\n  C -> body\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:non_data, source, "non_data.cure")
    {:ok, opener} = SourceRegistry.span(registry, :non_data, 0, 4)
    {:ok, scrutinee} = SourceRegistry.span(registry, :non_data, 5, 10)
    {:ok, branch} = SourceRegistry.span(registry, :non_data, 13, 22)
    {:ok, pattern} = SourceRegistry.span(registry, :non_data, 13, 14)

    errors = [
      {:source_context, :with_scrutinee_not_data,
       %{
         actual_type: {:float_type},
         opener_span: opener,
         scrutinee_span: scrutinee,
         with_arms: [%{span: branch}],
         with_form: :ordinary
       }},
      {:source_context, :match_scrutinee_not_data,
       %{
         actual_type: {:float_type},
         scrutinee_span: scrutinee,
         branch_patterns: [%{kind: :constructor, name: "C", pattern_span: pattern}]
       }}
    ]

    for error <- errors do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.suggestions != []
    end

    with_diagnostic = errors |> hd() |> TypeAdapter.from_error()
    assert with_diagnostic.primary.span == scrutinee
    assert Enum.map(with_diagnostic.secondary, & &1.span) == [opener, branch]

    match_diagnostic = errors |> Enum.at(1) |> TypeAdapter.from_error()
    assert match_diagnostic.primary.span == pattern
    assert hd(match_diagnostic.secondary).span == scrutinee

    rendered = Renderer.plain(match_diagnostic, registry, width: 80)
    assert rendered =~ "CONSTRUCTOR PATTERNS CANNOT MATCH FLOAT [E093]"
    assert rendered =~ "this expression has type `Float`"
    assert rendered =~ "Hint: Use a variable or wildcard"
  end

  test "mixed with branches single out a unique authored form" do
    source = "A -> a\nB -> b\nC | C -> c\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:mixed_with, source, "mixed_with.cure")
    {:ok, first} = SourceRegistry.span(registry, :mixed_with, 0, 6)
    {:ok, second} = SourceRegistry.span(registry, :mixed_with, 7, 13)
    {:ok, outlier} = SourceRegistry.span(registry, :mixed_with, 14, 24)

    error =
      {:source_context, :with_mixed_rematch_arms,
       %{
         with_arms: [
           %{style: :ordinary, span: first},
           %{style: :ordinary, span: second},
           %{style: :rematch, span: outlier}
         ]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == outlier
    assert Enum.map(direct.secondary, & &1.span) == [first, second]
    assert direct.payload.outlier_branch == 2

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "Possible outlier: only one branch uses the rematch"
    assert rendered =~ "possible outlier: this is the only rematch"
    assert rendered =~ "Hint: Make every branch use the same `with` form"
  end

  test "indexed with proof failures label the proof, scrutinee, and every branch" do
    source = "value proof pf\nA -> a\nB -> b\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:indexed_with, source, "indexed_with.cure")
    {:ok, scrutinee} = SourceRegistry.span(registry, :indexed_with, 0, 5)
    {:ok, proof} = SourceRegistry.span(registry, :indexed_with, 6, 14)
    {:ok, first} = SourceRegistry.span(registry, :indexed_with, 15, 21)
    {:ok, second} = SourceRegistry.span(registry, :indexed_with, 22, 28)

    error =
      {:source_context, {:with_indexed_scrutinee_unsupported, :"Main#Vector"},
       %{
         proof_name: "pf",
         proof_span: proof,
         scrutinee_span: scrutinee,
         branch_patterns: [%{span: first}, %{span: second}]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == proof
    assert Enum.map(direct.secondary, & &1.span) == [scrutinee, first, second]
    assert direct.payload.family == "Vector"

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "INDEXED WITH CANNOT BIND A VALUE PROOF [E093]"
    assert rendered =~ "this value belongs to indexed family `Vector`"
    assert rendered =~ "this branch would need an indexed value equation"
    assert rendered =~ "Hint: Remove `proof pf`"
  end

  test "dependent match inference points to the responsible branch and enclosing match" do
    source = "match value\nCons(x) -> x\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:dependent_match, source, "dependent.cure")
    {:ok, match_span} = SourceRegistry.span(registry, :dependent_match, 0, 5)
    {:ok, branch_span} = SourceRegistry.span(registry, :dependent_match, 12, 24)

    error =
      {:source_context, {:cannot_infer_dependent_match, {:data, :Result, [], []}},
       %{
         opener_span: match_span,
         checking: :tail,
         branch_patterns: [%{name: "Cons", span: branch_span}]
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == branch_span
    assert hd(direct.secondary).span == match_span
    refute inspect(direct.payload) =~ "{:data"

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "DEPENDENT MATCH RESULT NEEDS AN ANNOTATION [E093]"
    assert rendered =~ "the `Cons` branch returns a type tied"
    assert rendered =~ "this match has no expected result type"
    assert rendered =~ "Hint: Add a result annotation to `tail`"
  end

  test "record update and projection failures preserve every authored role" do
    source = "Point{base | value: 1}\nbase.value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:records, source, "records.cure")
    {:ok, record_name} = SourceRegistry.span(registry, :records, 0, 5)
    {:ok, base} = SourceRegistry.span(registry, :records, 6, 10)
    {:ok, receiver} = SourceRegistry.span(registry, :records, 23, 27)
    {:ok, field} = SourceRegistry.span(registry, :records, 28, 33)

    update =
      {:source_context, {:record_update_base_mismatch, %{record: :"Main#Point", actual: :"Std.Int#Int"}},
       %{record_name_span: record_name, base_span: base}}

    projection =
      {:source_context, {:projection_not_a_record, :"Std.Int#Int"},
       %{field: "value", receiver_span: receiver, field_span: field}}

    for error <- [update, projection] do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.suggestions != []
    end

    assert TypeAdapter.from_error(update).primary.span == base
    assert hd(TypeAdapter.from_error(update).secondary).span == record_name
    assert TypeAdapter.from_error(projection).primary.span == receiver
    assert hd(TypeAdapter.from_error(projection).secondary).span == field
  end

  test "dependent projection labels the receiver, declaration, and prerequisite fields" do
    source = "flag value box.value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:dependent_record, source, "dependent_record.cure")
    {:ok, flag_decl} = SourceRegistry.span(registry, :dependent_record, 0, 4)
    {:ok, value_decl} = SourceRegistry.span(registry, :dependent_record, 5, 10)
    {:ok, receiver} = SourceRegistry.span(registry, :dependent_record, 11, 14)
    {:ok, field} = SourceRegistry.span(registry, :dependent_record, 15, 20)

    error =
      {:source_context, {:dependent_record_projection, :"Main#Box", "value"},
       %{
         field_span: field,
         receiver_span: receiver,
         dependent_fields: ["flag"],
         projected_field_declaration: %{type_span: value_decl},
         dependent_field_declarations: %{"flag" => %{type_span: flag_decl}}
       }}

    direct = TypeAdapter.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.primary.span == field
    assert Enum.map(direct.secondary, & &1.span) == [receiver, value_decl, flag_decl]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "`VALUE` CANNOT BE PROJECTED WITHOUT ITS DEPENDENCY [E093]"
    assert rendered =~ "`flag` supplies part of `value`'s type"
    assert rendered =~ "Hint: Pattern-match `Box` and bind flag, value together"
  end

  test "typed and forced pattern failures retain annotation, binder, and constructor roles" do
    source = "Ctor(value: Bool) .index\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:patterns, source, "patterns.cure")
    {:ok, constructor} = SourceRegistry.span(registry, :patterns, 0, 17)
    {:ok, binder} = SourceRegistry.span(registry, :patterns, 5, 10)
    {:ok, annotation} = SourceRegistry.span(registry, :patterns, 12, 16)
    {:ok, forced} = SourceRegistry.span(registry, :patterns, 18, 24)

    typed =
      {:source_context, {:typed_pattern_type_mismatch, {:variable, [], "Bool"}},
       %{
         constructor: :"Main#Ctor",
         binder: "value",
         annotated_type: {:data, :Bool, [], []},
         field_type: {:data, :Int, [], []},
         annotation_span: annotation,
         binder_span: binder,
         constructor_pattern_span: constructor
       }}

    mismatch =
      {:source_context, {:forced_pattern_mismatch, {:ctor, :Wrong, []}, {:ctor, :Expected, []}},
       %{
         constructor: :"Main#Ctor",
         implicit_name: "index",
         forced_pattern_span: forced,
         named_implicit_span: forced,
         constructor_name_span: constructor
       }}

    for error <- [typed, mismatch] do
      direct = TypeAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.suggestions != []
    end

    assert TypeAdapter.from_error(typed).primary.span == annotation
    assert Enum.map(TypeAdapter.from_error(typed).secondary, & &1.span) == [binder, constructor]
    assert TypeAdapter.from_error(mismatch).primary.span == forced

    rendered = Renderer.plain(TypeAdapter.from_error(typed), registry, width: 80)
    assert rendered =~ "`VALUE` IS ANNOTATED AS `BOOL`, BUT `CTOR` STORES `INT`"
    assert rendered =~ "Hint: Change the annotation to `Int`"
  end
end
