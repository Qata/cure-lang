defmodule Cure.Compiler.RefinementTypeSurfaceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer}

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "proof-backed refinement syntax parses and prints losslessly" do
    source = """
    mod RefinementSurface
      type PositiveNatural = {value: Nat | IsPositive(value)}
    end
    """

    ast = parse!(source)
    printed = Printer.quoted_to_string(ast)
    assert printed =~ "{value: Nat | IsPositive(value)}"
    reparsed = parse!(printed)
    assert Printer.quoted_to_string(reparsed) == printed
  end
end
