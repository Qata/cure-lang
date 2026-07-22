defmodule Cure.Compiler.MacroSyntaxTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Errors, Lexer, MacroSyntax, Parser, Token}
  alias Cure.Diagnostic.Renderer
  alias Cure.MetaAST.Metadata

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

  # Recursively drop diagnostic metadata so round-trip equality is position-insensitive.
  defp strip(t) when is_list(t),
    do:
      Enum.reject(
        t,
        &match?(
          {k, _}
          when k in [:line, :col, :span, :name_span, :callee_span, :construct_span, :source_info, :provenance],
          &1
        )
      )
      |> Enum.map(&strip/1)

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

  test "syntax reflection preserves reorderable named-argument labels without source-range opacity" do
    ast = expr!("move(from: old, to: next)")
    assert {:syn_node, :function_call, attrs, [_old, _next]} = MacroSyntax.to_syntax(ast)
    assert {:arg_labels, {:s_list, [{:s_str, "from"}, {:s_str, "to"}]}} in attrs
    refute Keyword.has_key?(attrs, :arg_label_spans)

    assert {:function_call, roundtrip_meta, _args} = MacroSyntax.from_syntax(MacroSyntax.to_syntax(ast))
    assert Keyword.fetch!(roundtrip_meta, :arg_labels) == ["from", "to"]
  end

  test "to_syntax records generic constructor spelling and arity metadata" do
    repr = MacroSyntax.to_syntax(expr!("Ping(value)"))

    assert {:syn_node, :function_call, attrs, _args} = repr
    assert {:pascal_case, {:s_bool, true}} in attrs
    assert {:constructor_key, {:s_atom, :"Ping/1"}} in attrs

    nullary = MacroSyntax.to_syntax(expr!("Ping"))
    assert {:syn_leaf, :variable, nullary_attrs, {:s_str, "Ping"}} = nullary
    assert {:pascal_case, {:s_bool, true}} in nullary_attrs
    assert {:constructor_key, {:s_atom, :"Ping/0"}} in nullary_attrs
  end

  test "to_syntax records a canonical atom for reflected variable names" do
    {:syn_leaf, :variable, attrs, {:s_str, "state"}} = MacroSyntax.to_syntax(expr!("state"))

    assert {:variable_name, {:s_atom, :state}} in attrs
  end

  test "source coordinates survive the syntax reflection boundary" do
    ast = {:variable, [line: 12, col: 7, scope: :local], "state"}

    assert {:syn_leaf, :variable, attrs, {:s_str, "state"}} = MacroSyntax.to_syntax(ast)
    assert {:source_line, {:s_int, 12}} in attrs
    assert {:source_col, {:s_int, 7}} in attrs

    assert MacroSyntax.from_syntax(MacroSyntax.to_syntax(ast)) == ast
  end

  test "canonical authored ranges survive syntax and Core reflection" do
    ast = expr!("g(1, x + 2)")
    reflected = ast |> MacroSyntax.to_syntax() |> MacroSyntax.to_core() |> MacroSyntax.from_core()
    round_tripped = MacroSyntax.from_syntax(reflected)

    assert Metadata.source_info(elem(round_tripped, 1)) == Metadata.source_info(elem(ast, 1))

    assert Enum.zip(elem(round_tripped, 2), elem(ast, 2))
           |> Enum.all?(fn {left, right} ->
             Metadata.source_info(elem(left, 1)) == Metadata.source_info(elem(right, 1))
           end)
  end

  test "to_syntax reflects a raw lexer Token without crashing" do
    # A `delayed raw until dedent` capture leaks unparsed Tokens into the macro
    # input; expansion_key/1 reflects that input via to_syntax. A Token is a
    # struct, so it must not fall into the plain-map synlit clause (which would
    # Enum.map over the struct and raise).
    tok = Token.new(:newline, "\n", 1, 60)
    assert {:syn_raw, repr} = MacroSyntax.to_syntax(tok)
    refute repr == :s_opaque
  end

  test "reflected Tokens are position-insensitive but content-distinguishing" do
    # The macro recursion guard (expansion_key/1) ignores source positions, so
    # two Tokens differing only in line/col must reflect equally; Tokens with
    # different type or value must reflect differently, or the guard would treat
    # two distinct raw bodies as the same expansion and drop one.
    base = MacroSyntax.to_syntax(Token.new(:atom, ":inc", 1, 1))
    moved = MacroSyntax.to_syntax(Token.new(:atom, ":inc", 9, 42))
    other_val = MacroSyntax.to_syntax(Token.new(:atom, ":dec", 1, 1))
    other_type = MacroSyntax.to_syntax(Token.new(:ident, ":inc", 1, 1))

    assert base == moved
    refute base == other_val
    refute base == other_type
  end

  test "caller scope is consumed before generated syntax reaches elaboration" do
    repr = {:syn_leaf, :variable, [{:scope, {:s_atom, :caller}}], {:s_str, "state"}}

    assert {:variable, [scope: :local], "state"} = MacroSyntax.from_syntax(repr)
  end

  test "from_syntax(to_syntax(ast)) round-trips up to source position" do
    for src <- ["g(1, x + 2)", "[1, 2, 3]", "\"hi\"", ":ok", "true", "3.5", "f()"] do
      ast = expr!(src)

      assert strip(MacroSyntax.from_syntax(MacroSyntax.to_syntax(ast))) == strip(ast),
             "round-trip failed for #{src}"
    end
  end

  test "quoted syntax survives reflection as an opaque syntax value" do
    ast = {:quoted_syntax, [line: 3], [{:computed_use, [keyword: "inner"], []}]}

    repr = MacroSyntax.to_syntax(ast)
    assert {:syn_quoted, {:syn_node, :computed_use, _, []}} = repr
    assert MacroSyntax.from_syntax(repr) == {:quoted_syntax, [], [{:computed_use, [keyword: "inner"], []}]}
  end

  test "quoted syntax round-trips through the closed Core bridge" do
    repr = {:syn_quoted, {:syn_leaf, :literal, [], {:s_int, 1}}}

    assert MacroSyntax.from_core(MacroSyntax.to_core(repr)) == repr
  end

  test "MacroResult wrappers decode without changing the Syntax representation" do
    repr = {:syn_leaf, :literal, [], {:s_int, 1}}
    expanded = {:ctor, :"Std.Syntax#Expanded", [MacroSyntax.to_core(repr)]}

    rejected =
      {:ctor, :"Std.Syntax#Rejected",
       [{:ctor, :"Std.List#Cons", [MacroSyntax.to_core(repr), {:ctor, :"Std.List#Nil", []}]}]}

    assert {:expanded, ^repr} = MacroSyntax.from_core_macro_result(expanded)
    assert {:rejected, [^repr]} = MacroSyntax.from_core_macro_result(rejected)
  end

  test "Std.Result wrappers decode as macro results" do
    repr = {:syn_leaf, :literal, [], {:s_int, 1}}
    ok = {:ctor, :"Std.Result#Ok", [MacroSyntax.to_core(repr)]}
    error = {:ctor, :"Std.Result#Error", [MacroSyntax.to_core(repr)]}

    assert {:expanded, ^repr} = MacroSyntax.from_core_macro_result(ok)
    assert {:rejected, [^repr]} = MacroSyntax.from_core_macro_result(error)
  end

  test "expansion validation rejects reflection-only raw and quoted values" do
    assert {:error, {:raw_syntax_in_expansion, []}} =
             MacroSyntax.validate_expansion({:syn_raw, {:s_int, 1}})

    assert {:error, {:quoted_syntax_in_expansion, [{:child, 0}]}} =
             MacroSyntax.validate_expansion(
               {:syn_node, :block, [], [{:syn_quoted, {:syn_leaf, :literal, [], {:s_int, 1}}}]}
             )

    assert :ok =
             MacroSyntax.validate_expansion({:syn_node, :block, [], [{:syn_leaf, :literal, [], {:s_int, 1}}]})
  end

  test "expansion validation reports every malformed generated-syntax location" do
    reflected = fn syntax -> {:syn_leaf, :holder, [], {:s_syntax, syntax}} end

    cases = [
      {{:syn_raw, {:s_int, 1}}, {:raw_syntax_in_expansion, []}},
      {{:syn_node, :block, [], [{:syn_quoted, {:syn_leaf, :literal, [], {:s_int, 1}}}]},
       {:quoted_syntax_in_expansion, [{:child, 0}]}},
      {:bad, {:malformed_expansion_syntax, []}},
      {{:syn_failure, :bad, :arguments}, {:malformed_expansion_syntax, []}},
      {{:syn_node, :block, [42], []}, {:malformed_expansion_attribute, [{:attribute, 0}]}},
      {{:syn_leaf, :literal, [], {:s_map, [42]}}, {:malformed_expansion_map, []}},
      {{:syn_leaf, :literal, [], :bad}, {:malformed_expansion_literal, []}},
      {reflected.(:bad), {:malformed_reflected_syntax, [{:syntax_literal}]}},
      {reflected.({:syn_node, :inner, [42], []}),
       {:malformed_reflected_attribute, [{:attribute, 0}, {:syntax_literal}]}},
      {reflected.({:syn_leaf, :inner, [], {:s_map, [42]}}), {:malformed_reflected_map, [{:syntax_literal}]}},
      {reflected.({:syn_leaf, :inner, [], :bad}), {:malformed_reflected_literal, [{:syntax_literal}]}},
      {reflected.({:syn_raw, :bad}), {:malformed_reflected_literal, [{:raw_literal}, {:syntax_literal}]}}
    ]

    Enum.each(cases, fn {syntax, reason} ->
      assert {:error, ^reason} = MacroSyntax.validate_expansion(syntax)
    end)
  end

  test "every generated-syntax integrity branch has dedicated diagnostic content" do
    cases = [
      {{:raw_syntax_in_expansion, []}, "Macro expansion contains raw syntax",
       "The generated expansion contains reflection-only raw syntax at the expansion root.",
       "Build structured `Syntax`; keep `Raw` values inside reflected metadata"},
      {{:quoted_syntax_in_expansion, [{:child, 0}]}, "Macro expansion contains quoted syntax",
       "The generated expansion still contains quoted syntax at `child[0]`.",
       "Splice or otherwise unquote the value before returning the expansion"},
      {{:malformed_expansion_syntax, []}, "Macro expansion syntax is malformed",
       "The generated expansion does not contain a valid `Node`, `Leaf`, or accepted failure value at the expansion root.",
       "Return a well-formed structured `Syntax` value"},
      {{:malformed_expansion_attribute, [{:attribute, 0}]}, "Macro expansion attribute is malformed",
       "A generated syntax attribute is not an atom-keyed literal pair at `{:attribute, 0}`.",
       "Use an atom key and a valid syntax literal value"},
      {{:malformed_expansion_map, []}, "Macro expansion map literal is malformed",
       "A generated syntax-map entry is not a key-value pair at the expansion root.",
       "Provide valid syntax-literal key-value pairs"},
      {{:malformed_expansion_literal, []}, "Macro expansion literal is malformed",
       "A generated syntax literal has the wrong shape or host value at the expansion root.",
       "Use a valid integer, float, string, boolean, atom, list, map, syntax, or opaque literal"},
      {{:malformed_reflected_syntax, [{:syntax_literal}]}, "Reflected syntax value is malformed",
       "Syntax stored inside generated metadata has an invalid node shape at `syntax literal`.",
       "Store a well-formed reflected `Syntax` value"},
      {{:malformed_reflected_attribute, [{:attribute, 0}, {:syntax_literal}]},
       "Reflected syntax attribute is malformed",
       "An attribute inside reflected syntax is not an atom-keyed literal pair at `syntax literal.{:attribute, 0}`.",
       "Use an atom key and a valid reflected literal value"},
      {{:malformed_reflected_map, [{:syntax_literal}]}, "Reflected syntax map is malformed",
       "A map stored inside reflected syntax contains an entry that is not a key-value pair at `syntax literal`.",
       "Provide valid reflected-literal key-value pairs"},
      {{:malformed_reflected_literal, [{:raw_literal}, {:syntax_literal}]}, "Reflected syntax literal is malformed",
       "A literal stored inside reflected syntax has the wrong shape or host value at `syntax literal.raw literal`.",
       "Use a valid reflected syntax literal"}
    ]

    Enum.each(cases, fn {reason, title, body, hint} ->
      {diagnostic, registry} = Errors.to_diagnostic(reason, "generated.cure", "")
      output = Renderer.plain(diagnostic, registry, width: 80)

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_syntax_integrity
      assert diagnostic.title == title
      assert String.replace(output, ~r/\s+/, " ") =~ String.replace(body, ~r/\s+/, " ")
      assert output =~ "Hint: " <> hint

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["message"] == title <> "\n\n" <> body
    end)
  end

  test "expansion validation permits reflection-only values in syntax metadata" do
    reflected =
      {:syn_node, :outer, [{:payload, {:s_syntax, {:syn_raw, {:s_int, 1}}}}], []}

    assert :ok = MacroSyntax.validate_expansion(reflected)
  end

  test "a regex literal reflects as its typed pure Cure constructor call" do
    ast = expr!("/foo/")
    repr = MacroSyntax.to_syntax(ast)

    assert {:syn_node, :function_call, attrs,
            [
              {:syn_leaf, :literal, pattern_attrs, {:s_str, "foo"}},
              {:syn_leaf, :literal, flags_attrs, {:s_str, ""}}
            ]} = repr

    assert {:name, {:s_str, "Std.Regex.literal"}} in attrs
    assert {:subtype, {:s_atom, :string}} in pattern_attrs
    assert {:subtype, {:s_atom, :string}} in flags_attrs
    assert MacroSyntax.from_syntax(repr) == ast
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

  test "a named_implicit_pat node (canonical {tag, meta, [inner]}) reflects without crashing" do
    ast = parse_stmt!("match v { vcons({k = .m}, h, r) -> h }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg0 | _]} = Keyword.get(ameta, :pattern)
    assert {:named_implicit_pat, nmeta, [_inner]} = arg0
    assert Keyword.get(nmeta, :name) == "k"

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

    assert {:ctor, :"Std.Syntax#Node",
            [{:atom_lit, :literal}, {:ctor, :"Std.List#Cons", _}, {:ctor, :"Std.List#Cons", _}]} = core

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

    assert {:ctor, :MkSyntax,
            [{:ctor, :"Std.Syntax#Leaf", _}, {:ctor, :"Std.Syntax#Raw", [{:ctor, :"Std.Syntax#SOpaque", []}]}]} =
             MacroSyntax.to_core_record("MkSyntax", ["x"], input)

    assert {:ctor, :EmptySyntax, [{:ctor, :"Std.Syntax#Raw", [{:ctor, :"Std.Syntax#SOpaque", []}]}]} =
             MacroSyntax.to_core_record("EmptySyntax", [], {:syn_node, :macro_input, [], []})
  end

  test "a derived rule record carries the reflected expansion context in its trailing field" do
    context = %{behaviour: :gen_server, callback: :handle_cast, arity: 2}
    input = MacroSyntax.with_context({:syn_node, :macro_input, [], []}, context)

    assert {:ctor, :SelfSyntax,
            [{:ctor, :"Std.Syntax#Node", [{:atom_lit, :callback_context}, attrs, {:ctor, :"Std.List#Nil", []}]}]} =
             MacroSyntax.to_core_record("SelfSyntax", [], input)

    assert {:ctor, :"Std.List#Cons", _} = attrs
  end

  test "a rule with no expansion context reflects a total, absent context" do
    assert {:syn_raw, :s_opaque} = MacroSyntax.context_syntax(nil)
    assert {:syn_node, :macro_input, [], []} = MacroSyntax.with_context({:syn_node, :macro_input, [], []}, nil)
  end

  test "the reflected expansion context round-trips through the Core bridge" do
    context = %{behaviour: :gen_server, callback: :handle_info, arity: 2, parameter_names: ["msg", "state"]}
    repr = MacroSyntax.context_syntax(context)

    assert MacroSyntax.from_core(MacroSyntax.to_core(repr)) == repr
    assert {:callback_context, attrs, []} = MacroSyntax.from_syntax(repr)
    assert attrs[:behaviour] == :gen_server
    assert attrs[:parameter_names] == ["msg", "state"]
  end
end
