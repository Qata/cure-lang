defmodule Cure.Elab.MacroRecursiveExpansionTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.MacroExpand
  alias Cure.Elab.Program

  test "nested computed macros normalize inside out before the outer macro runs" do
    source = """
    mod M
      use Std.Syntax

      macro Inner
        syntax inner <x: Code> computed by build_inner
          example inner 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "inner" =>
            "starts with inner"

      macro Outer
        syntax outer <x: Code> computed by build_outer
          example outer 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "outer" =>
            "starts with outer"

      fn build_inner(input: InnerSyntax) -> Syntax = input.x
      fn build_outer(input: OuterSyntax) -> Syntax = input.x
      fn f(n: Int) -> Int = outer inner n
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "the recursive reducer enforces an explicit AST budget" do
    assert {:ok, env} = Program.elaborate("mod M\n  fn f() -> Int = 0\n")

    assert {:error, {:macro_expansion_budget, :node_count}} =
             MacroExpand.expand({:literal, [subtype: :integer], 0}, env, max_nodes: 0)
  end
end
