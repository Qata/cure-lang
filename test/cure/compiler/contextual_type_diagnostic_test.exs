defmodule Cure.Compiler.ContextualTypeDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
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
end
