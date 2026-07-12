defmodule Cure.Compiler.MacroRawTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, MacroRaw, Parser, Token}

  test "parser preserves a delimited raw hole" do
    source = """
    macro Datalog
      syntax datalog <rules: raw until dedent> becomes rules
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)
    assert [{:raw_hole, %{name: "rules", delimiter: "dedent"}}] = rule.segments
  end

  test "raw capture stops at the delimiter and preserves the prefix" do
    tokens = [
      %Token{type: :identifier, value: "a", line: 2, col: 1},
      %Token{type: :dedent, value: nil, line: 3, col: 1},
      %Token{type: :identifier, value: "after", line: 3, col: 1}
    ]

    assert {:ok, captured, rest} = MacroRaw.capture(tokens, "dedent")
    assert Enum.map(captured, & &1.value) == ["a"]
    assert [%Token{value: "after"}] = rest
  end

  test "raw capture reports a missing delimiter" do
    token = %Token{type: :identifier, value: "a", line: 1, col: 1}
    assert {:error, {:missing_raw_delimiter, "dedent"}} = MacroRaw.capture([token], "dedent")
  end
end
