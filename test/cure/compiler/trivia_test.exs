defmodule Cure.Compiler.TriviaTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer

  test "lexer collects every comment and blank run as positioned trivia" do
    src = """
    mod M

    # leading comment
    fn f() -> Int = 1  # trailing comment
    """

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t.cure", trivia: true)

    texts = for {:comment, t, _l, _c} <- trivia, do: String.trim(t)
    assert "leading comment" in texts
    assert "trailing comment" in texts
    assert Enum.any?(trivia, &match?({:blank, _, _}, &1))
  end

  test "a blank line that contains only indentation whitespace still counts as blank" do
    # Pins the fix for reusing lex_indentation/1's own blank-line branch
    # (lexer.ex:210-231, which strips leading whitespace via measure_indent/1
    # BEFORE checking for end-of-line) rather than a fresh "newline-only line"
    # definition that would miss this case. The blank line between `x` and `y`
    # below has two leading spaces (mirroring the block's own indent), which a
    # naive "line is exactly empty" check would fail to classify as blank.
    src = "mod M\nfn f() -> Int =\n  let x = 1\n  \n  x\n"

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t2.cure", trivia: true)

    assert Enum.any?(trivia, &match?({:blank, _, _}, &1)),
           "a whitespace-only blank line was not collected as trivia: #{inspect(trivia)}"
  end
end
