defmodule Cure.Compiler.ContextualTypeDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Span
  alias Cure.Diagnostic.Renderer

  test "a declared return mismatch retains its authored checking context" do
    source = "fn answer() -> Int = 1.0\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "answer.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "answer.cure", source)

    assert diagnostic.code == "E093"
    assert diagnostic.title == "Annotation does not match"
    assert diagnostic.payload.origin.owner == :answer
    assert diagnostic.payload.expression_category == :literal
    assert diagnostic.primary.span.start_column == 22
    assert Renderer.plain(diagnostic, registry) =~ "type written in its annotation"
  end

  test "a missing implicit instance retains the authored call context" do
    source = "mod M\n  fn has(x: t, y: t) -> Bool = x == y\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "implicit.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "implicit.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.expectation_origin == :implicit
    assert diagnostic.payload.checking == :==
    assert rendered =~ "implicit"
    assert rendered =~ "2 |   fn has(x: t, y: t) -> Bool = x == y"
  end

  test "a real conditional mismatch reports the authored guard" do
    source = "fn main() -> Int = if 1 then 2 else 3\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "condition.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "condition.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :condition
    assert diagnostic.primary.span.start_column == 23
    assert rendered =~ "CONDITION IS NOT BOOLEAN"
    assert rendered =~ "1 | fn main() -> Int = if 1 then 2 else 3"
    assert rendered =~ "this condition has the wrong type"
  end

  test "a branch failure names the checking function and authored arms" do
    reason =
      {:source_context, :branch_type,
       %{
         line: 8,
         column: 5,
         length: 20,
         checking: :multiply_int_successor_coefficient,
         expression_category: :pattern_match,
         expectation_origin: :annotation,
         branch_patterns: ["FromNat", "NegativeSuccessor"]
       }}

    source = "\n\n\n\n\n\n\n    match coefficient\n"
    {diagnostic, registry} = Errors.to_diagnostic(reason, "proof_int_order.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.branches == ["FromNat", "NegativeSuccessor"]
    assert rendered =~ "MULTIPLY_INT_SUCCESSOR_COEFFICIENT"
    assert rendered =~ "FromNat"
    assert rendered =~ "NegativeSuccessor"
    assert rendered =~ "proof_int_order.cure:8:5"
    assert rendered =~ "8 |     match coefficient"
    assert rendered =~ "|     ^"
  end

  test "an enriched branch failure labels every arm and singles out the outlier" do
    source = "match coefficient\n  FromNat(n) -> first\n  NegativeSuccessor(n) -> second\n"

    first = raw_span(source, "FromNat(n) -> first", 2, 3)
    second = raw_span(source, "NegativeSuccessor(n) -> second", 3, 3)

    reason =
      {:source_context,
       {:branch_type,
        %{
          constructor: :"Std.Int#NegativeSuccessor",
          actual: {:data, :Actual, [], []},
          expected: {:data, :Expected, [], []}
        }},
       %{
         line: 2,
         column: 3,
         checking: :multiply_int_successor_coefficient,
         expression_category: :pattern_match,
         expectation_origin: :annotation,
         branch_patterns: [
           %{name: "FromNat", span: first},
           %{name: "NegativeSuccessor", span: second}
         ]
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "proof_int_order.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.primary.message == "compare this branch with the declared result"
    assert [secondary] = diagnostic.secondary
    assert secondary.message == "possible outlier: this branch has the incompatible type"
    assert diagnostic.payload.failing_branch == :"Std.Int#NegativeSuccessor"
    assert rendered =~ "Possible outlier"
    assert rendered =~ "FromNat(n) -> first"
    assert rendered =~ "NegativeSuccessor(n) -> second"
    assert rendered =~ "compare this branch with the declared result"
    assert rendered =~ "possible outlier: this branch has the incompatible type"
  end

  test "a singleton branch type is called out when the other arms agree" do
    common = {:data, :Common, [], []}
    outlier = {:data, :Outlier, [], []}

    reason =
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
         checking: :three_way_match,
         branch_patterns: [%{name: "A"}, %{name: "B"}, %{name: "C"}]
       }}

    {diagnostic, _registry} = Errors.to_diagnostic(reason, "branches.cure", "")

    assert Renderer.plain(diagnostic) =~ "only the `C` branch has type"
    assert diagnostic.payload.branch_types |> Enum.map(& &1.branch) == [:A, :B, :C]
  end

  test "a call argument conversion retains its argument origin and caret" do
    source = "fn main() -> Int = use(1, \"bad\")\n"
    argument = raw_span(source, "\"bad\"", 1, 27)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 27,
         length: 5,
         span: argument,
         expectation_span: argument,
         checking: :use,
         argument_index: 1,
         expression_category: :literal,
         expectation_origin: :call_argument
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "call.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Argument has the wrong type"
    assert diagnostic.payload.origin.kind == :call_argument
    assert diagnostic.payload.origin.owner == :use
    assert diagnostic.payload.origin.index == 1
    assert diagnostic.primary.span.start_column == 27
    assert rendered =~ "Argument 2 of `use`"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Int = use(1, \"bad\")"
    assert rendered =~ "this argument has the wrong type"
  end

  test "an operator operand conversion retains its operand origin and caret" do
    source = "fn main() -> Bool = \"bad\" == 1\n"
    operand = raw_span(source, "\"bad\"", 1, 21)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 21,
         length: 5,
         span: operand,
         expectation_span: operand,
         checking: :==,
         argument_index: 0,
         expression_category: :literal,
         expectation_origin: :operator_operand
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "operator.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Operator cannot use this value"
    assert diagnostic.payload.origin.kind == :operator_operand
    assert diagnostic.payload.origin.owner == :==
    assert diagnostic.payload.origin.index == 0
    assert diagnostic.primary.span.start_column == 21
    assert rendered =~ "The `==` operator cannot use this operand type"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Bool = \"bad\" == 1"
    assert rendered =~ "this operator operand has the wrong type"
  end

  test "a conditional guard conversion retains its condition origin and caret" do
    source = "fn main() -> Int = if 1 then 2 else 3\n"
    condition = raw_span(source, "1", 1, 23)

    reason =
      {:source_context, {:conversion_failure, "Int", "Bool"},
       %{
         line: 1,
         column: 23,
         length: 1,
         span: condition,
         expectation_span: condition,
         checking: :if,
         expression_category: :literal,
         expectation_origin: :condition
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "condition.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Condition is not boolean"
    assert diagnostic.payload.origin.kind == :condition
    assert diagnostic.payload.origin.owner == :if
    assert diagnostic.primary.span.start_column == 23
    assert rendered =~ "A condition must produce `Bool`"
    assert rendered =~ "Expected: Bool"
    assert rendered =~ "Found:    Int"
    assert rendered =~ "1 | fn main() -> Int = if 1 then 2 else 3"
    assert rendered =~ "this condition has the wrong type"
  end

  test "a tuple element conversion retains its element origin and caret" do
    source = "fn main() -> Pair = %[1, \"bad\"]\n"
    element = raw_span(source, "\"bad\"", 1, 26)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 26,
         length: 5,
         span: element,
         expectation_span: element,
         checking: :tuple,
         argument_index: 1,
         expression_category: :literal,
         expectation_origin: :element
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "tuple.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Collection element has the wrong type"
    assert diagnostic.payload.origin.kind == :element
    assert diagnostic.payload.origin.owner == :tuple
    assert diagnostic.payload.origin.index == 1
    assert diagnostic.primary.span.start_column == 26
    assert rendered =~ "Element 2 of this collection"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Pair = %[1, \"bad\"]"
    assert rendered =~ "this collection element has the wrong type"
  end

  test "a constructor argument conversion retains its constructor origin and caret" do
    source = "fn main() -> Maybe = Some(\"bad\")\n"
    argument = raw_span(source, "\"bad\"", 1, 27)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 27,
         length: 5,
         span: argument,
         expectation_span: argument,
         checking: :Some,
         argument_index: 0,
         expression_category: :literal,
         expectation_origin: :constructor_argument
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "constructor.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Constructor argument has the wrong type"
    assert diagnostic.payload.origin.kind == :constructor_argument
    assert diagnostic.payload.origin.owner == :Some
    assert diagnostic.payload.origin.index == 0
    assert diagnostic.primary.span.start_column == 27
    assert rendered =~ "Argument 1 of constructor `Some`"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Maybe = Some(\"bad\")"
    assert rendered =~ "this constructor argument has the wrong type"
  end

  test "a record field conversion retains the authored field origin and caret" do
    source = "Point{name: \"bad\"}\n"
    value = raw_span(source, "\"bad\"", 1, 13)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 13,
         length: 5,
         span: value,
         expectation_span: value,
         checking: :name,
         argument_index: 0,
         expression_category: :literal,
         expectation_origin: :record_field
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Record field has the wrong type"
    assert diagnostic.payload.origin.kind == :record_field
    assert diagnostic.payload.origin.owner == :name
    assert diagnostic.primary.span.start_column == 13
    assert rendered =~ "Field `name` does not match"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | Point{name: \"bad\"}"
    assert rendered =~ "this record field has the wrong type"
  end

  test "a real one-field record mismatch points at the field value" do
    source =
      "mod M\n" <>
        "  rec Point\n" <>
        "    x: Int\n" <>
        "  fn bad() -> Point = Point{x: \"bad\"}\n" <>
        "end\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "record.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :record_field
    assert diagnostic.payload.origin.owner == :x
    assert diagnostic.primary.span.start_line == 4
    assert rendered =~ "Field `x` does not match"
    assert rendered =~ "4 |   fn bad() -> Point = Point{x: \"bad\"}"
    assert rendered =~ "this record field has the wrong type"
  end

  test "a typed pattern mismatch points at the authored annotation" do
    source = "n: Bool -> 1\n"
    annotation = raw_span(source, "Bool", 1, 4)
    type_ast = {:variable, [source_info: %Cure.MetaAST.SourceInfo{whole: annotation}], "Bool"}

    reason =
      {:source_context, {:typed_pattern_type_mismatch, type_ast},
       %{
         line: 1,
         column: 4,
         length: 4,
         span: annotation,
         expectation_span: annotation,
         checking: :pattern,
         expression_category: :pattern,
         expectation_origin: :pattern,
         argument_index: 0
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "pattern.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Pattern annotation does not match"
    assert diagnostic.primary.span.start_column == 4
    assert rendered =~ "This pattern's annotation is incompatible"
    assert rendered =~ "1 | n: Bool -> 1"
    assert rendered =~ "change the pattern or its type annotation"
  end

  test "a unary operator operand retains its source caret" do
    source = "not 1\n"
    operand = raw_span(source, "1", 1, 5)

    reason =
      {:source_context, {:conversion_failure, "Int", "Bool"},
       %{
         line: 1,
         column: 5,
         length: 1,
         span: operand,
         expectation_span: operand,
         checking: :not,
         expression_category: :literal,
         expectation_origin: :operator_operand,
         argument_index: 0
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "unary.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Operator cannot use this value"
    assert diagnostic.payload.origin.owner == :not
    assert diagnostic.primary.span.start_column == 5
    assert rendered =~ "The `not` operator cannot use this operand type"
    assert rendered =~ "1 | not 1"
    assert rendered =~ "this operator operand has the wrong type"
  end

  test "a real call result mismatch names and highlights the call" do
    source =
      "fn id(x: Int) -> Int = x\n" <>
        "fn main() -> Bool = id(1)\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "call_result.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "call_result.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :call_result
    assert diagnostic.payload.origin.owner == "id"
    assert diagnostic.primary.span.start_line == 2
    assert rendered =~ "CALL RESULT HAS THE WRONG TYPE"
    assert rendered =~ "The result of `id` does not match"
    assert rendered =~ "2 | fn main() -> Bool = id(1)"
    assert rendered =~ "this call result has the wrong type"
  end

  test "a real chained application reports an application result" do
    source =
      "fn mk() -> (Nat) -> Nat = fn(y) -> y\n" <>
        "fn main() -> Bool = mk()(Z())\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "application.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "application.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :application
    assert diagnostic.primary.span.start_line == 2
    assert rendered =~ "APPLICATION HAS THE WRONG TYPE"
    assert rendered =~ "This application"
    assert rendered =~ "2 | fn main() -> Bool = mk()(Z())"
    assert rendered =~ "this application has the wrong type"
  end

  defp raw_span(source, needle, line, column) do
    {start_byte, byte_length} = :binary.match(source, needle)

    %Span{
      source_id: "nofile",
      path: "nofile",
      start_byte: start_byte,
      end_byte: start_byte + byte_length,
      start_line: line,
      start_column: column,
      end_line: line,
      end_column: column + String.length(needle)
    }
  end
end
