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

  # Parse a bare statement (e.g. `match ... { ... }`) standalone, no `fn` wrapper.
  defp parse_stmt!(src) do
    {:ok, tokens} = Lexer.tokenize(src <> "\n", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
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

  test "a binary-segment size expression (an AST, not a scalar) round-trips faithfully" do
    ast = expr!("<<x::size(n)>>")
    # {:literal, [subtype: :bytes,...], [{:bin_segment, [size: {:variable,...,"n"}, ...], [{:variable,...,"x"}]}]}
    repr = MacroSyntax.to_syntax(ast)
    back = MacroSyntax.from_syntax(repr)

    assert {:literal, _, [{:bin_segment, seg_meta, [{:variable, _, "x"}]}]} = back
    assert {:variable, _, "n"} = Keyword.fetch!(seg_meta, :size)
  end

  test "a match_arm with an `impossible` body (third = [nil], not [ast]) does not crash" do
    ast = parse_stmt!("match v { vcons(h, r) -> impossible }")
    # {:pattern_match, _, [_scrutinee, {:match_arm, meta, [nil]}]}
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, _, [nil]} = arm

    repr = MacroSyntax.to_syntax(arm)
    back = MacroSyntax.from_syntax(repr)
    assert {:match_arm, _, [nil]} = back
  end

  test "a named_implicit_pat node (a 4-tuple, not {tag,meta,third}) does not crash" do
    ast = parse_stmt!("match v { vcons({k = .m}, h, r) -> h }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg0 | _]} = Keyword.get(ameta, :pattern)
    assert {:named_implicit_pat, _, "k", _inner} = arg0

    # Must not raise (FunctionClauseError) -- reflecting the whole arm walks
    # into arg0 via the pattern= meta attr.
    repr = MacroSyntax.to_syntax(arm)
    assert is_tuple(MacroSyntax.from_syntax(repr))
  end

  test "a list-valued meta attr (selective-import item list) round-trips faithfully" do
    ast = {:import, [items: ["foo", "bar"], source: "Std.String", import_type: :use, language: :cure], []}

    repr = MacroSyntax.to_syntax(ast)
    back = MacroSyntax.from_syntax(repr)

    assert {:import, meta, []} = back
    assert Keyword.fetch!(meta, :items) == ["foo", "bar"]
  end

  test "a map-valued meta attr (interface default-method table) round-trips faithfully" do
    parsed =
      parse_stmt!("""
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
        fn ne(x: a, y: a) -> Bool = true
      end
      """)

    # A top-level `interface` (no `mod` wrapper) parses as a `:block` with the
    # trailing stray `end` token as a sibling -- dig out the interface node.
    ast =
      case parsed do
        {:block, _, items} -> Enum.find(items, &match?({:interface, _, _}, &1))
        other -> other
      end

    assert {:interface, imeta, _methods} = ast
    assert %{"ne" => _} = Keyword.fetch!(imeta, :defaults)

    repr = MacroSyntax.to_syntax(ast)
    back = MacroSyntax.from_syntax(repr)

    assert {:interface, bmeta, _} = back
    defaults = Keyword.fetch!(bmeta, :defaults)
    assert is_map(defaults)
    assert {:literal, _, true} = Map.fetch!(defaults, "ne")
  end

  test "Std.Syntax mirror values encode to and decode from Core constructors" do
    repr =
      {:syn_node, :literal, [{:subtype, {:s_atom, :integer}}], [{:syn_leaf, :literal, [], {:s_int, 7}}]}

    core = MacroSyntax.to_core(repr)
    assert {:ctor, :Node, [{:atom_lit, :literal}, {:ctor, :Cons, _}, {:ctor, :Cons, _}]} = core
    assert MacroSyntax.from_core(core) == repr
  end

  test "Core bridge preserves strings, nested syntax, maps, and opaque values" do
    repr =
      {:syn_leaf, :raw, [{:payload, {:s_map, [{{:s_str, "k"}, {:s_syntax, {:syn_leaf, :x, [], :s_opaque}}}]}}],
       {:s_list, [{:s_str, "hi"}, :s_opaque]}}

    assert MacroSyntax.from_core(MacroSyntax.to_core(repr)) == repr
  end

  test "Core bridge preserves an author failure carrying reflected syntax arguments" do
    repr =
      {:syn_failure, :BadInput, [{:syn_leaf, :variable, [], {:s_str, "n"}}]}

    assert MacroSyntax.from_core(MacroSyntax.to_core(repr)) == repr
  end

  test "a derived rule record encodes reflected syntax fields as a Core constructor" do
    input = {:syn_node, :macro_input, [], [{:syn_leaf, :variable, [], {:s_str, "n"}}]}

    assert {:ctor, :MkSyntax, [{:ctor, :Leaf, _}]} = MacroSyntax.to_core_record("MkSyntax", input)
    assert {:ctor, :EmptySyntax, []} = MacroSyntax.to_core_record("EmptySyntax", {:syn_node, :macro_input, [], []})
  end
end
