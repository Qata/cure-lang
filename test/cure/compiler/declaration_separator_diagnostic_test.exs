defmodule Cure.Compiler.DeclarationSeparatorDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, &match?({:declaration_separator_missing, _}, &1))
    assert {:declaration_separator_missing, _} = error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "a GADT constructor signature gets an exact colon insertion" do
    source = "mod M\n  type A = MkA\n  type Box indices ()\n    Mk A -> Box\n"
    {error, {diagnostic, registry}} = diagnostic(source, "ctor_colon.cure")

    assert {:declaration_separator_missing,
            %{
              kind: :gadt_constructor_colon_missing,
              family: "Box",
              declaration: "Mk"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CONSTRUCTOR SIGNATURE NEEDS A COLON [E094] ------------------ ctor_colon.cure

             The constructor `Mk` in `Box` needs `:` between its name and type signature.

             A valid continuation here starts with ':'.

             at ctor_colon.cure:4:8
             4 |     Mk A -> Box
               |     -- ^ this is the constructor name; insert `:` before this constructor signature

             Hint: Insert `:` before the constructor signature
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {4, 8}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ": ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 3, "character" => 7},
             "end" => %{"line" => 3, "character" => 7}
           }
  end

  test "a record field declaration gets an exact colon insertion" do
    source = "rec Person\n  name String\n"
    {error, {diagnostic, registry}} = diagnostic(source, "record_colon.cure")

    assert {:declaration_separator_missing,
            %{
              kind: :record_field_colon_missing,
              family: "Person",
              declaration: "name"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- RECORD FIELD NEEDS A COLON [E094] ------------------------- record_colon.cure

             The field `name` in record `Person` needs `:` between its name and declared
             type.

             A valid continuation here starts with ':'.

             at record_colon.cure:2:8
             2 |   name String
               |   ---- ^ this is the record field name; insert `:` before this field type

             Hint: Insert `:` before the field type
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 8}
    assert insertion.start_byte == insertion.end_byte
  end
end
