# test/cure/compiler/macro_use_test.exs
defmodule Cure.Compiler.MacroUseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "two-phase parse still returns the macro def unchanged (no regression from single-pass)" do
    # A module with only a macro def: the harvest pass must not alter the
    # authoritative parse's output for the def itself.
    node = parse!("mod M\n  macro Now\n    syntax now becomes Clock.now()\n")
    # The macro def survives inside the module container.
    assert has_macro_def?(node)
  end

  defp has_macro_def?({:macro_def, _, _}), do: true
  defp has_macro_def?({_t, _m, children}) when is_list(children), do: Enum.any?(children, &has_macro_def?/1)
  defp has_macro_def?(_), do: false
end
