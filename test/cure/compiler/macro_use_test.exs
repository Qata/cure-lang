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

  test "a zero-hole local macro use-site expands to its template" do
    # `now` is defined as a macro; a later `now` use-site expands to Clock.now().
    node =
      parse!("mod M\n  macro Now\n    syntax now becomes Clock.now()\n  fn f() = now\n")
    # Find `f`'s body; it must be the expanded Clock.now() call, not a bare
    # `{:variable, _, "now"}`.
    body = find_fn_body(node, "f")
    assert {:function_call, meta, _} = body
    assert Keyword.get(meta, :name) in ["Clock.now", "now"]  # Clock.now() call shape
    refute match?({:variable, _, "now"}, body)
  end

  # Walk to a function_def's body by name.
  defp find_fn_body({:function_def, meta, [body]}, name) do
    if to_string(Keyword.get(meta, :name)) == name, do: body, else: nil
  end
  defp find_fn_body({_t, _m, children}, name) when is_list(children),
    do: Enum.find_value(children, &find_fn_body(&1, name))
  defp find_fn_body(_, _), do: nil

  test "a local macro cannot claim a reserved dispatch keyword (sup stays the supervisor container)" do
    # `sup` is one of parse_prefix/1's existing :identifier soft-keyword names.
    # A macro rule that claims it must NOT be able to shadow the supervisor
    # container: `sup Worker` must still produce it.
    node =
      parse!("mod M\n  macro Trap\n    syntax sup becomes Clock.now()\n  sup Worker\n")

    assert has_supervisor?(node)
  end

  # A container node is either the supervisor itself, or (e.g. the enclosing
  # module) a container whose children must still be searched — so this clause
  # must both check container_type AND recurse, never short-circuit.
  defp has_supervisor?({:container, meta, children}) do
    Keyword.get(meta, :container_type) == :supervisor or
      (is_list(children) and Enum.any?(children, &has_supervisor?/1))
  end
  defp has_supervisor?({_t, _m, children}) when is_list(children),
    do: Enum.any?(children, &has_supervisor?/1)
  defp has_supervisor?(_), do: false
end
