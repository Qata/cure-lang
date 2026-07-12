defmodule Cure.Compiler.MacroDefParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Cure containers close purely by DEDENT — no literal `end` is consumed by a
  # container parser, and `end` is a reserved keyword that would otherwise lex as
  # a stray second top-level node. So the macro sources below have no `end`.
  # `Parser.parse/2` returns the BARE node for a single top-level form (never a
  # list), so tests bind `node = parse!(...)`.

  test "an empty macro container parses to a {:macro_def, meta, []} node" do
    node = parse!("macro Every\n")
    assert {:macro_def, meta, []} = node
    assert meta[:name] == "Every"
  end

  test "`macro` NOT followed by an identifier stays a plain variable (non-breaking)" do
    node = parse!("macro + 1\n")
    assert {:binary_op, _, [{:variable, _, "macro"}, _rhs]} = node
  end

  test "a bare-keyword syntax rule captures its keyword and template" do
    node = parse!("macro Now\n  syntax now becomes Clock.now()\n")
    assert {:macro_def, _meta, [rule]} = node
    assert rule.kind == :syntax
    assert rule.keyword == "now"
    assert rule.segments == []
    assert {:function_call, _, _} = rule.template
    assert Map.has_key?(rule, :progress)
  end

  test "a body line that isn't a recognized rule keyword records a parse error" do
    {:ok, tokens} = Lexer.tokenize("macro Bad\n  oops\n", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:expected, :syntax_rule, :got, _, _, _}, &1))
  end
end
