# test/cure/compiler/macro_hygiene_test.exs
defmodule Cure.Compiler.MacroHygieneTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(tokens, emit_events: false)
  end

  # Find the first {:fresh_name, _, _} anywhere in an AST. A macro's rule is
  # stored as a plain Elixir map (`%{template: ..., segments: ..., ...}`),
  # not an AST tuple, so the generic tuple-recursion clause below can never
  # reach a rule's `:template` on its own — unwrap it explicitly.
  defp find_fresh(%{template: t}), do: find_fresh(t)
  defp find_fresh({:fresh_name, _, _} = f), do: f
  defp find_fresh({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &find_fresh/1)
  defp find_fresh(_), do: nil

  test "a <fresh Name> in a becomes template parses to a {:fresh_name, meta, name} marker" do
    {:ok, ast} =
      parse("mod M\n  macro G\n    syntax g becomes let <fresh h> = 100 in h\n")
    assert {:fresh_name, _meta, "h"} = find_fresh(ast)
  end
end
