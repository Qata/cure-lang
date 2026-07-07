defmodule Cure.Elab.DeclHygieneTest do
  @moduledoc """
  Module-level declaration hygiene: a module must not bind the same type or
  constructor name twice. Both go through silent `Map.put` overwrites
  (`env.families` / `env.ctors` / `env.ctor_to_family`), so a duplicate silently
  loses one declaration — and a constructor mapped to two families is a soundness
  hole (Cure has no type-directed constructor disambiguation). Idris/Agda/Lean all
  reject these.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  test "duplicate type declaration in one module is rejected" do
    src = "mod DupType\n  type Foo = A\n  type Foo = B\nend\n"
    assert {:error, {:duplicate_type, :Foo}} = elaborate(src)
  end

  test "duplicate constructor within one type is rejected" do
    src = "mod DupCtor\n  type Foo = A | A\nend\n"
    assert {:error, {:duplicate_constructor, :A}} = elaborate(src)
  end

  test "constructor name shared across two types in a module is rejected (no ctor namespacing)" do
    src = "mod DupCtorX\n  type Foo = C | D\n  type Bar = C | E\nend\n"
    assert {:error, {:duplicate_constructor, :C}} = elaborate(src)
  end

  test "distinct types and constructors still elaborate" do
    src = "mod OKdecl\n  type Foo = A | B\n  type Bar = C | D\nend\n"
    assert {:ok, _} = elaborate(src)
  end

  test "duplicate parameter name in a function is rejected" do
    src = "mod DupParam\n  fn f(x: Int, x: Int) -> Int = x\nend\n"
    assert {:error, {:duplicate_parameter, :x}} = elaborate(src)
  end

  test "distinct parameter names still elaborate" do
    src = "mod OKParam\n  fn g(x: Int, y: Int) -> Int = x\nend\n"
    assert {:ok, _} = elaborate(src)
  end
end
