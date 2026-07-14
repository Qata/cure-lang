defmodule Cure.Compiler.MacroRawTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, MacroModule, MacroRaw, Parser, Token}

  test "parser preserves a delimited raw hole" do
    source = """
    macro Datalog
      syntax datalog <rules: raw until dedent> becomes rules
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)
    assert [{:raw_hole, %{name: "rules", delimiter: "dedent"}}] = rule.segments
  end

  test "raw capture stops at the delimiter and preserves the prefix" do
    tokens = [
      %Token{type: :identifier, value: "a", line: 2, col: 1},
      %Token{type: :dedent, value: nil, line: 3, col: 1},
      %Token{type: :identifier, value: "after", line: 3, col: 1}
    ]

    assert {:ok, captured, rest} = MacroRaw.capture(tokens, "dedent")
    assert Enum.map(captured, & &1.value) == ["a"]
    assert [%Token{value: "after"}] = rest
  end

  test "raw capture reports a missing delimiter" do
    token = %Token{type: :identifier, value: "a", line: 1, col: 1}
    assert {:error, {:missing_raw_delimiter, "dedent"}} = MacroRaw.capture([token], "dedent")
  end

  test "computed macro uses bind raw spans without consuming the enclosing dedent" do
    source = """
    macro Datalog
      syntax datalog <rules: raw until dedent> computed by build
    datalog
      rule one
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:block, _, children}} = Parser.parse(tokens, emit_events: false)

    assert [{:computed_use, _, [_elab, {:macro_input, _, [{:raw_tokens, meta, captured}]}]}] =
             Enum.filter(children, &match?({:computed_use, _, _}, &1))

    assert Keyword.get(meta, :delimiter) == "dedent"
    assert Enum.any?(captured, &(&1.value == "rule"))
  end

  test "generated raw fillers assemble through the reader-tier delimiter" do
    source = "macro Datalog\n  syntax datalog <rules: raw until dedent> becomes rules\n"
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)
    assert {:ok, use_site} = Cure.Compiler.MacroFuzz.assemble_use_site(rule, %{"rules" => {:raw_text, "item"}})
    assert {:raw_tokens, _, captured} = Parser.expand_example([rule], use_site)
    assert Enum.map(captured, & &1.value) == ["item"]
  end

  test "module rules execute to ordinary AST without loading a module" do
    source = """
    macro Board
      syntax module <decl: Code> becomes decl
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, rules}} = Parser.parse(tokens, emit_events: false)
    rule = Enum.find(rules, &(&1[:module_rule] == true))

    assert {:ok, {:literal, _meta, 1}} =
             MacroModule.execute_module_rule(rule, rules, %{"decl" => {:int_lit, 1}})

    assert {:error, :not_a_module_rule} =
             MacroModule.execute_module_rule(%{kind: :syntax, module_rule: false}, rules, %{})
  end

  test "open categories compose extensions and reject closed categories" do
    base = [%{kind: :open_category, name: "Clause"}, %{kind: :syntax, keyword: "base", category: "Clause"}]
    extension = [%{kind: :syntax, keyword: "extra", category: "Clause"}]
    assert {:ok, rules} = MacroModule.compose_open_categories(base, extension)
    assert Enum.map(rules, & &1[:keyword]) == [nil, "base", "extra"]

    closed = [%{kind: :syntax, keyword: "other", category: "Other"}]

    assert {:error, {:closed_category_extension, ["Other"]}} =
             MacroModule.compose_open_categories(base, closed)
  end
end
