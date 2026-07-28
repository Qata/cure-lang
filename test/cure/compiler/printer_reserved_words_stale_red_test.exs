defmodule Cure.Compiler.Printer.ReservedWordsStaleRedTest do
  @moduledoc """
  `Cure.Compiler.Printer.@reserved_words` is a hand-copy of
  `Cure.Compiler.Lexer.@keywords` that is missing `opaque`, `primitive`,
  `quote`, `band`, `bor`, `bxor`, `bsl`, `bsr`, `bnot`. A function defined
  with one of those names via a backtick escape (legal per
  `test/cure/elab/backtick_operator_names_test.exs`) must be re-emitted
  backtick-quoted by the printer to round-trip; because the missing words
  aren't in `@reserved_words`, the printer emits them bare, which re-lexes
  as the keyword/operator token instead of an identifier and fails to
  reparse as the same definition.
  """
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, file: "m.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "m.cure", emit_events: false)
    ast
  end

  @src """
  mod M
    fn `band`(a: Int, b: Int) -> Int = a
  end
  """

  test "a function named `band` is printed backtick-quoted so it re-parses" do
    ast = parse!(@src)
    out = Printer.quoted_to_string(ast)

    # Desired post-fix behavior: the printer re-quotes the reserved word so
    # the emitted source still names the function `band` via backticks.
    assert out =~ "`band`",
           "expected printed source to backtick-quote the reserved name `band`, got:\n#{out}"

    # And the round-trip contract: printed source must re-lex/re-parse to an
    # equivalent AST (a `band`-named function), not misparse/crash because
    # `band` now lexes as the `:band_op` keyword.
    reparsed = parse!(out)

    assert contains_function?(reparsed, "band"),
           "expected the re-parsed AST to still contain a function named `band`, got:\n#{inspect(reparsed)}"
  end

  defp contains_function?({:function_def, meta, _body}, name),
    do: Keyword.get(meta, :name) == name

  defp contains_function?({_tag, _meta, children}, name) when is_list(children),
    do: Enum.any?(children, &contains_function?(&1, name))

  defp contains_function?(children, name) when is_list(children),
    do: Enum.any?(children, &contains_function?(&1, name))

  defp contains_function?(_ast, _name), do: false
end
