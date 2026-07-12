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

  # Find fn body by name (function_def carries name in meta, body as [body]).
  defp fn_body({:function_def, meta, [body]}, name),
    do: if(to_string(Keyword.get(meta, :name)) == name, do: body)

  defp fn_body({_t, _m, ch}, name) when is_list(ch), do: Enum.find_value(ch, &fn_body(&1, name))
  defp fn_body(_, _), do: nil

  test "a <fresh> template binder is gensym'd so it cannot capture a same-named use-site arg" do
    # addg's template binds `g` via <fresh g>; the use-site passes its own `g`
    # (the parameter) as the hole. After expansion the binder must be a fresh
    # name (not "g"), distinct from the substituted parameter `g`, so no capture.
    {:ok, ast} =
      parse(
        "mod M\n  macro AddG\n    syntax addg <e: Code> becomes let <fresh g> = 100 in e + g\n  fn f(g: Int) -> Int = addg g\n"
      )

    body = fn_body(ast, "f")
    # body = let <gensym> = 100 in g + <gensym>
    {:block, _, [assign, plus]} = body
    {:assignment, _, [{:variable, _, binder}, _]} = assign
    {:binary_op, _, [{:variable, _, lhs}, {:variable, _, rhs}]} = plus

    # binder was freshened away from "g"
    refute binder == "g"
    # the hole-substituted param stays "g" (NOT captured/freshened)
    assert lhs == "g"
    # the template's own reference `g` was freshened to match the binder
    assert rhs == binder
    # and there is no leftover unexpanded marker ANYWHERE in the expanded body
    refute find_fresh(body)
  end
end
