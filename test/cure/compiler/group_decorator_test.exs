defmodule Cure.Compiler.GroupDecoratorTest do
  @moduledoc """
  `@group(:g)` placed ABOVE `mod` attaches to the module container (spec
  2026-07-10-group-decorator-placement). This test file grows across the
  expand→migrate→contract tasks; Task 4 adds the hard-error case.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  # Parse a source string to its AST, asserting no parse errors.
  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # The module container node in a parsed program (unwraps a {:block, _, items}).
  defp module_node(ast) do
    items =
      case ast do
        {:block, _, xs} -> xs
        xs when is_list(xs) -> xs
        other -> [other]
      end

    Enum.find(items, &match?({:container, meta, _} when is_list(meta), &1))
  end

  test "@group above mod attaches the group to the module container meta" do
    ast = parse!("@group(:core)\nmod M\n  fn f(x: Int) -> Int = x\nend\n")
    {:container, meta, _body} = module_node(ast)
    assert {:group, [{:literal, _, :core}]} = Keyword.get(meta, :decorator)
  end
end
