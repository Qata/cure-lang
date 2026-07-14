defmodule Cure.Doc.MermaidTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Mermaid

  test "renders generic lifted module metadata" do
    callbacks = [%{name: :start, arity: 2}, %{name: :stop, arity: 1}]

    ast =
      {:lift_module,
       [
         behaviour: :user_defined,
         module: "Cure.Example",
         callbacks: callbacks,
         declarations: [],
         line: 1
       ], []}

    out = Mermaid.render(ast)

    assert out =~ "classDiagram"
    assert out =~ "Cure_Example"
    assert out =~ "behaviour user_defined"
    assert out =~ "callbacks 2"
    assert out =~ "start/2 callback"
    assert out =~ "stop/1 callback"
  end

  test "renders a transparent lifted module from source" do
    assert {:ok, ast} = Cure.Compiler.parse_source("sup Cure.DocSup\n", emit_events: false)
    out = Mermaid.render(ast)

    assert out =~ "classDiagram"
    assert out =~ "Cure_DocSup"
    assert out =~ "behaviour supervisor"
  end

  test "returns nil for non-lifted input" do
    assert Mermaid.render({:literal, [], 42}) == nil
  end
end
