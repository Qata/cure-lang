# test/cure/compiler/macro_example_check_test.exs
defmodule Cure.Compiler.MacroExampleCheckTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp macro_def!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    find = fn find, n ->
      case n do
        {:macro_def, _, _} = m -> m
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end
    find.(find, ast)
  end

  test "expand_example runs an example's captured use-site through the rule" do
    {:macro_def, _, rules} =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    rule = Enum.find(rules, &(&1[:kind] == :syntax))
    [ex] = rule.examples

    result = Parser.expand_example(rules, ex.use_site)
    # every 500  ==>  Timer.repeat(500)
    assert {:function_call, meta, [{:literal, _, 500}]} = result
    assert Keyword.get(meta, :name) == "Timer.repeat"
  end
end
