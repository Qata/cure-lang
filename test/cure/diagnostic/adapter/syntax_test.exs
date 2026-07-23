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

  test "pattern-only forms retain their authored punctuation and body" do
    source = ".value {field = pattern}\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:patterns, source, "patterns.cure")

    {:ok, dot} = SourceRegistry.span(registry, :patterns, 0, 1)
    {:ok, value} = SourceRegistry.span(registry, :patterns, 1, 6)
    {:ok, implicit} = SourceRegistry.span(registry, :patterns, 7, 24)
    {:ok, field} = SourceRegistry.span(registry, :patterns, 8, 13)
    {:ok, pattern} = SourceRegistry.span(registry, :patterns, 16, 23)

    forced =
      {:source_context, {:forced_pattern_not_in_pattern, []},
       %{span: value, opener_span: dot, body_span: value, checking: :run}}

    named =
      {:source_context, {:named_implicit_not_in_pattern, []},
       %{
         span: implicit,
         name_span: field,
         body_span: pattern,
         checking: :run
       }}

    for error <- [forced, named] do
      direct = SyntaxAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E093"
      assert direct.primary
      assert direct.secondary != []
      assert direct.suggestions != []
    end

    forced_diagnostic = SyntaxAdapter.from_error(forced)
    assert forced_diagnostic.primary.span == dot
    assert hd(forced_diagnostic.secondary).span == value

    rendered = Renderer.plain(forced_diagnostic, registry, width: 80)
    assert rendered =~ "FORCED VALUE APPEARS OUTSIDE A PATTERN"
    assert rendered =~ "Hint: Remove the leading dot"

    for error <- [
          {:forced_pattern_not_in_pattern, :value},
          {:named_implicit_not_in_pattern, :field}
        ] do
      assert Adapter.from_error(error) == SyntaxAdapter.from_error(error)
    end
  end
end
