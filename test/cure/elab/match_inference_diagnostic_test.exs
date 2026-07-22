defmodule Cure.Elab.MatchInferenceDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a constructor-free inferred match labels the complete match and every uninformative pattern" do
    source =
      "mod M\n  type Color = Red | Blue\n  fn choose(c: Color) = match c\n    _ -> Red()\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "match_inference.cure")

    assert {:cannot_infer_match_type, %{reason: :no_constructor_arm}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MATCH RESULT NEEDS AN ANNOTATION [E093] ---------------- match_inference.cure

             Cure is inferring the result type of this match, but none of its patterns names
             a constructor. A wildcard or variable arm can handle values of many data types,
             so it does not reveal the family or dependent result that the branches must
             share.

             at match_inference.cure:3:25
             3 |   fn choose(c: Color) = match c
               >                         ^^^^^^^
             4 |     _ -> Red()
               > ^^^^^^^^^^^^^^ this match has no constructor arm to guide inference
               >     - this pattern does not identify a constructor

             Hint: Add a result annotation to the enclosing declaration, or include a constructor pattern that identifies the matched data family
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 24, 3, 14)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(3, 4, 3, 5)
           ]

    assert lsp["data"]["payload"] == %{
             "expression_category" => "pattern_match",
             "kind" => "cannot_infer_match_type",
             "reason" => "no_constructor_arm"
           }

    refute inspect(diagnostic.payload) =~ "source_info"
  end

  test "an inferred match on a non-data value labels both the match and scrutinee" do
    source = "mod M\n  fn choose(n: Type) = match n\n    _ -> n\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "non_data_match.cure")

    assert {:cannot_infer_match_type, %{reason: :scrutinee_not_data}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MATCH TARGET DOES NOT HAVE A DATA TYPE [E093] ----------- non_data_match.cure

             Cure can only infer an unannotated match from a scrutinee whose type has
             constructors. This value does not infer as a data family, so its patterns cannot
             determine a shared result type.

             at non_data_match.cure:2:24
             2 |   fn choose(n: Type) = match n
               >                        ^^^^^^^
               >                              - this value does not infer as a data family
             3 |     _ -> n
               > ^^^^^^^^^^ this match cannot infer a result from its target

             Hint: Match a value of a declared data type, or add a result annotation that gives this match an expected type
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 23, 2, 10)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(1, 29, 1, 30)
           ]
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
