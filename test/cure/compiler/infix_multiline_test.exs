defmodule Cure.Compiler.InfixMultilineTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false) do
      Parser.parse(tokens, emit_events: false, prelude_macros: false)
    end
  end

  test "builtin infix operators accept an indented right operand on the next line" do
    for source <- [
          "true or\n  false",
          "true and\n  false",
          "1 +\n  2",
          "1 ==\n  2",
          "1 ..\n  2",
          "value.\n  field",
          "mailbox <-|\n  message"
        ] do
      assert {:ok, _ast} = parse(source), "failed to parse:\n#{source}"
    end
  end

  test "a multiline expression may chain operators inside one continuation layout" do
    assert {:ok, _ast} =
             parse("""
             true or
               false or
               true
             """)
  end

  test "user-defined infix operators receive the same newline continuation" do
    assert {:ok, _ast} =
             parse("""
             precedencegroup Join
               associativity: left
             infix `<?>` : Join
             fn combine(left: Int, right: Int) -> Int = left
             fn example() -> Int = 1 <?>
               2
             """)
  end

  test "operators beginning a continuation line are also declaration-driven" do
    assert {:ok, _ast} = parse("mailbox\n  <-| message")

    assert {:ok, _ast} =
             parse("""
             precedencegroup Join
               associativity: left
             infix `<?>` : Join
             fn combine(left: Int, right: Int) -> Int = left
             fn example() -> Int = 1
               <?> 2
             """)
  end
end
