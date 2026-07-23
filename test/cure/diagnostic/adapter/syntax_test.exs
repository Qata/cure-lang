defmodule Cure.Diagnostic.Adapter.SyntaxTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Adapter
  alias Cure.Diagnostic.Adapter.Syntax, as: SyntaxAdapter
  alias Cure.Diagnostic.Renderer
  alias Cure.Diagnostic.SourceRegistry

  test "grade syntax producers are owned directly and retain token repairs" do
    source = "[h | t] :linear :liner c :affine\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:grades, source, "grades.cure")

    {:ok, pattern} = SourceRegistry.span(registry, :grades, 0, 7)
    {:ok, binding_grade} = SourceRegistry.span(registry, :grades, 8, 15)
    {:ok, typo} = SourceRegistry.span(registry, :grades, 16, 22)
    {:ok, missing_type} = SourceRegistry.span(registry, :grades, 25, 32)

    errors = [
      {:graded_let_requires_variable, %{grade: :linear, pattern_span: pattern, grade_span: binding_grade}},
      {:unknown_grade,
       %{
         grade: :liner,
         supported: [:erased, :linear, :affine],
         span: typo
       }},
      {:grade_requires_type, %{name: "c", grade: :affine, span: missing_type}}
    ]

    for error <- errors do
      direct = SyntaxAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.suggestions != []
    end

    typo_diagnostic = SyntaxAdapter.from_error(Enum.at(errors, 1))

    assert [
             %{
               applicability: :machine_applicable,
               edits: [%{span: ^typo, replacement: ":linear"}]
             }
           ] = typo_diagnostic.suggestions

    rendered = Renderer.plain(typo_diagnostic, registry, width: 80)
    assert rendered =~ "UNKNOWN RELEVANCE GRADE [E093]"
    assert rendered =~ "^^^^^^ this grade is not defined"
    assert rendered =~ "Hint: Replace it with `:linear`"
  end

  test "unowned errors are rejected by the family boundary" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      SyntaxAdapter.from_error({:unknown_syntax_producer, %{}})
    end
  end
end
