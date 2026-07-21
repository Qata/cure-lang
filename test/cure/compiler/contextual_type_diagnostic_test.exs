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
    assert rendered =~ "multiply_int_successor_coefficient"
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
