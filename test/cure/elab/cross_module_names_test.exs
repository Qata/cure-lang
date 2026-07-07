defmodule Cure.Elab.CrossModuleNamesTest do
  @moduledoc """
  A module is a namespace: each `mod` compiles to its own BEAM module (`Cure.A`,
  `Cure.B`), so two SIBLING modules sharing a function / type / constructor name is
  legitimate (the stdlib has `map` in five modules, `show`/`eq` in six). Cross-module
  collisions are resolved by the E-layer resolution/rekey machinery (LOCKED
  type-shadowing Approach B), NOT by outright rejection. The within-module
  duplicate checks must therefore be scoped PER MODULE — a repeat only within one
  module is the silent-overwrite soundness bug.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp check(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Program.check_ast(ast)
  end

  test "two sibling modules may share a function name" do
    src = "mod A\n  fn foo(x: Int) -> Int = x\nend\nmod B\n  fn foo(x: Int) -> Int = 99\nend\n"
    assert {:ok, _} = check(src)
  end

  test "two sibling modules may share a type name" do
    src = "mod A\n  type Foo = MkA\nend\nmod B\n  type Foo = MkB\nend\n"
    assert {:ok, _} = check(src)
  end

  test "two sibling modules may share a constructor name" do
    src = "mod A\n  type Foo = C\nend\nmod B\n  type Bar = C\nend\n"
    assert {:ok, _} = check(src)
  end

  test "a duplicate WITHIN one module is still rejected (function)" do
    src = "mod A\n  fn foo(x: Int) -> Int = x\n  fn foo(y: Int) -> Int = y\nend\n"
    assert {:error, {:duplicate_definition, :foo}} = check(src)
  end

  test "a duplicate WITHIN one module is still rejected (constructor across two types)" do
    src = "mod A\n  type Foo = C | D\n  type Bar = C | E\nend\n"
    assert {:error, {:duplicate_constructor, :C}} = check(src)
  end
end
