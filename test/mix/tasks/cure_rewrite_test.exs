defmodule Mix.Tasks.Cure.RewriteTest do
  use ExUnit.Case, async: false

  test "a conditional embedded in a call-argument list is left unrewritten (paren-context), not turned into unparseable output" do
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"

    ast =
      Cure.Compiler.Lexer.tokenize(src, file: "t.cure", emit_events: false)
      |> then(fn {:ok, toks} -> Cure.Compiler.Parser.parse(toks, file: "t.cure", emit_events: false) end)
      |> then(fn {:ok, ast} -> ast end)

    new_ast = Mix.Tasks.Cure.Rewrite.rewrite(ast)
    out = Cure.Compiler.Printer.quoted_to_string(new_ast)

    refute out =~ "pickup"
    # Full reparse (lex AND parse), not just tokenize -- tokenizing alone does
    # not prove the output is syntactically valid.
    assert {:ok, toks2} = Cure.Compiler.Lexer.tokenize(out, file: "t.cure", emit_events: false)
    assert {:ok, _ast2} = Cure.Compiler.Parser.parse(toks2, file: "t.cure", emit_events: false)
  end
end
