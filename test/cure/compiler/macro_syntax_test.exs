defmodule Cure.Compiler.MacroSyntaxTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, MacroSyntax}

  # Parse the RHS of `fn f() = <expr>` to get a real expression AST.
  defp expr!(src) do
    {:ok, tokens} = Lexer.tokenize("fn f() = #{src}\n", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)

    find = fn find, n ->
      case n do
        {:function_def, _, [body]} -> body
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    find.(find, ast)
  end

  # Recursively drop :line/:col so round-trip equality is position-insensitive.
  defp strip(t) when is_list(t),
    do: Enum.reject(t, &match?({k, _} when k in [:line, :col], &1)) |> Enum.map(&strip/1)

  defp strip(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&strip/1) |> List.to_tuple()

  defp strip(t), do: t

  test "to_syntax builds a Node/Leaf repr preserving tag + semantic attrs" do
    ast = expr!("g(1, x)")
    # {:function_call, [name: "g", ...], [{:literal,_,1}, {:variable,_,"x"}]}
    repr = MacroSyntax.to_syntax(ast)
    assert {:syn_node, :function_call, attrs, [arg1, arg2]} = repr
    assert {:name, {:s_str, "g"}} in attrs
    assert {:syn_leaf, :literal, _, {:s_int, 1}} = arg1
    assert {:syn_leaf, :variable, _, {:s_str, "x"}} = arg2
  end

  test "from_syntax(to_syntax(ast)) round-trips up to source position" do
    for src <- ["g(1, x + 2)", "[1, 2, 3]", "\"hi\"", ":ok", "true", "3.5", "f()"] do
      ast = expr!(src)

      assert strip(MacroSyntax.from_syntax(MacroSyntax.to_syntax(ast))) == strip(ast),
             "round-trip failed for #{src}"
    end
  end

  test "an exotic scalar value (regex tuple) reflects opaquely without crashing" do
    ast = expr!("~r/foo/")
    # Node tag is :literal (subtype: :regex in meta), NOT a bare :regex tag —
    # only the scalar VALUE ({body, flags}) is exotic.
    repr = MacroSyntax.to_syntax(ast)
    assert {:syn_leaf, :literal, attrs, :s_opaque} = repr
    assert {:subtype, {:s_atom, :regex}} in attrs
    # round-trips to a literal leaf (value not faithfully recovered — opaque this slice)
    assert {:literal, _, nil} = MacroSyntax.from_syntax(repr)
  end
end
