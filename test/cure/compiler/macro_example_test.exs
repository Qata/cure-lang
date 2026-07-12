# test/cure/compiler/macro_example_test.exs
defmodule Cure.Compiler.MacroExampleTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp syntax_rule({:macro_def, _, rules}), do: Enum.find(rules, &(&1[:kind] == :syntax))
  defp syntax_rule({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &syntax_rule/1)
  defp syntax_rule(_), do: nil

  test "an example expands sub-block attaches to its syntax rule" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    rule = syntax_rule(node)
    assert [ex] = rule.examples
    # use_site captured as raw tokens: every 500
    assert Enum.map(ex.use_site, & &1.value) == ["every", 500]
    # expected expansion captured as AST
    assert {:expansion, {:function_call, _, _}} = ex.expected
  end

  test "a type-only example pin (`expands : Type`) is captured as {:type, _}" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands : Int\n"
      )

    rule = syntax_rule(node)
    assert [%{expected: {:type, _}}] = rule.examples
  end

  test "a syntax rule with no example has an empty examples list (non-breaking)" do
    node = parse!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert syntax_rule(node).examples == []
  end
end
