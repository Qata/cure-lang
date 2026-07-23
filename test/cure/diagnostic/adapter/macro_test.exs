defmodule Cure.Diagnostic.Adapter.MacroTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Adapter
  alias Cure.Diagnostic.Adapter.Macro, as: MacroAdapter
  alias Cure.Diagnostic.Renderer
  alias Cure.Diagnostic.SourceRegistry

  test "syntax-family fields and captures retain authored repairs" do
    source = "stte payload other\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:macro, source, "macro.cure")

    {:ok, field} = SourceRegistry.span(registry, :macro, 0, 4)
    {:ok, capture} = SourceRegistry.span(registry, :macro, 5, 12)
    {:ok, first} = SourceRegistry.span(registry, :macro, 13, 18)

    errors = [
      {:unknown_syntax_family_field,
       %{
         family: "Definition",
         field: "stte",
         valid_fields: ["state", "events"],
         span: field
       }},
      {:missing_syntax_family_field, %{family: "Definition", field: "state", span: field}},
      {:unknown_macro_obligation_capture,
       %{
         interface: "Show",
         capture: "payload",
         available_captures: ["paylod", "state"],
         span: capture
       }},
      {:unit_type_reserved, %{name: "Duration", span: field, unit_span: first}},
      {:duplicate_syntax_family_field, %{field: "state", span: field, first_span: first}}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.primary
      assert direct.suggestions != []
    end

    typo = MacroAdapter.from_error(hd(errors))

    assert [
             %{
               applicability: :machine_applicable,
               edits: [%{span: ^field, replacement: "state"}]
             }
           ] = typo.suggestions

    rendered = Renderer.plain(typo, registry, width: 80)
    assert rendered =~ "UNKNOWN SYNTAX-FAMILY FIELD [E092]"
    assert rendered =~ "^^^^ this field is not declared by the family"
    assert rendered =~ "Hint: Replace it with `state`"
  end

  test "unowned errors are rejected by the macro family boundary" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      MacroAdapter.from_error({:unknown_macro_producer, %{}})
    end
  end
end
