# test/cure/compiler/macro_explain_test.exs
defmodule Cure.Compiler.MacroExplainTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp explain_entry({:macro_def, _, rules}), do: Enum.find(rules, &(&1[:kind] == :explain))
  defp explain_entry({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &explain_entry/1)
  defp explain_entry(_), do: nil

  test "an explain block parses its clauses (category + keyword points) onto the macro_def" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    Duration =>\n      \"needs a duration\"\n    keyword \"every\" =>\n      \"a repeat rule starts with every\"\n"
      )

    ex = explain_entry(node)
    assert ex, "expected an :explain entry in the macro_def rules"
    points = Enum.map(ex.clauses, & &1.point)
    assert {:category, "Duration"} in points
    assert {:keyword, "every"} in points
  end

  test "a malformed explain point (stray '=>' with no preceding point) is a recorded parse error, not a crash" do
    {:ok, tokens} =
      Lexer.tokenize(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    => \"oops\"\n",
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:expected, :explain_point, :got, _, _, _}, &1))
  end
end
