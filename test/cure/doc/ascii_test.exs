defmodule Cure.Doc.AsciiTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Ascii

  test "renders generic lifted module metadata" do
    callbacks = [%{name: :init, arity: 1}, %{name: :handle, arity: 2}]

    ast =
      {:lift_module,
       [
         behaviour: :user_defined,
         module: "Cure.Example",
         callbacks: callbacks,
         declarations: [{:function_def, [], []}],
         line: 1
       ], []}

    out = Ascii.render(ast)

    assert out =~ "module Cure.Example"
    assert out =~ "behaviour: user_defined"
    assert out =~ "init/1"
    assert out =~ "handle/2"
    assert out =~ "declarations: 1"
  end

  test "renders a transparent lifted module from source" do
    assert {:ok, ast} = Cure.Compiler.parse_source("app Cure.DocApp\n", emit_events: false)
    out = Ascii.render(ast)

    assert out =~ "module Cure.DocApp"
    assert out =~ "behaviour: application"
  end

  test "returns nil for non-lifted input" do
    assert Ascii.render({:literal, [], 0}) == nil
  end

  test "render_file includes lifted modules and accepts the generic filter" do
    src = """
    app Cure.DocApp
    """

    path = Path.join(System.tmp_dir!(), "cure_ascii_test_#{System.unique_integer([:positive])}.cure")

    try do
      File.write!(path, src)
      assert {:ok, output} = Ascii.render_file(path, filter: :lifted)
      assert output =~ "module Cure.DocApp"
      assert {:ok, ""} = Ascii.render_file(path, filter: :fsm)
    after
      File.rm!(path)
    end
  end
end
