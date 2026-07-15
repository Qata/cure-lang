defmodule Cure.Compiler.MacroDefParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Cure containers close purely by DEDENT — no literal `end` is consumed by a
  # container parser, and `end` is a reserved keyword that would otherwise lex as
  # a stray second top-level node. So the macro sources below have no `end`.
  # `Parser.parse/2` returns the BARE node for a single top-level form (never a
  # list), so tests bind `node = parse!(...)`.

  test "an empty macro container parses to a {:macro_def, meta, []} node" do
    node = parse!("macro Every\n")
    assert {:macro_def, meta, []} = node
    assert meta[:name] == "Every"
  end

  test "`macro` NOT followed by an identifier stays a plain variable (non-breaking)" do
    node = parse!("macro + 1\n")
    assert {:binary_op, _, [{:variable, _, "macro"}, _rhs]} = node
  end

  test "a bare-keyword syntax rule captures its keyword and template" do
    node = parse!("macro Now\n  syntax now becomes Clock.now()\n")
    assert {:macro_def, _meta, [rule]} = node
    assert rule.kind == :syntax
    assert rule.keyword == "now"
    assert rule.segments == []
    assert {:function_call, _, _} = rule.template
    assert Map.has_key?(rule, :progress)
  end

  test "a body line that isn't a recognized rule keyword records a parse error" do
    {:ok, tokens} = Lexer.tokenize("macro Bad\n  oops\n", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:expected, :syntax_rule, :got, _, _, _}, &1))
  end

  test "a syntax rule with a typed hole captures name + kind in order" do
    node = parse!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert {:macro_def, _m, [rule]} = node
    assert rule.keyword == "every"
    assert [{:hole, hole}] = rule.segments
    assert hole.name == "t"
    assert hole.kind == "Duration"
  end

  test "a syntax rule records its declared category and module-rule marker" do
    node =
      parse!("macro Reducer\n  syntax module <decls: Code> is Reducer.Module becomes decls\n")

    assert {:macro_def, _m, [rule]} = node
    assert rule.category == "Reducer.Module"
    assert rule.module_rule
  end

  test "a contextual syntax rule defers proof until its use-site context" do
    node = parse!("macro Ops\n  syntax send <pid: Code> <message: Code> contextual becomes tell(pid, message)\n")
    assert {:macro_def, _m, [rule]} = node
    assert rule.contextual
  end

  test "a syntax family records typed sections and cardinality" do
    node =
      parse!("""
      macro ActorContainers
        syntax family ActorDefinition
          state Type
          optional messages Type
          repeated route Route
          one_or_more dependency ModuleName
      """)

    assert {:macro_def, _meta, [family]} = node
    assert family.kind == :syntax_family
    assert family.name == "ActorDefinition"

    assert Enum.map(family.fields, &{&1.name, &1.shape, &1.cardinality}) == [
             {"state", "Type", :required},
             {"messages", "Type", :optional},
             {"route", "Route", :repeated},
             {"dependency", "ModuleName", :one_or_more}
           ]
  end

  test "a structured macro header records accepts and expands with" do
    node =
      parse!("""
      macro actor <name: ModuleName>
        syntax family ActorDefinition
          state Type
        accepts ActorDefinition
        expands with derive_actor
      """)

    assert {:macro_def, meta, [family, accepts, expands]} = node

    assert family.kind == :syntax_family
    assert family.name == "ActorDefinition"

    assert Keyword.get(meta, :leading_segments) == [
             {:hole, %{name: "name", kind: "ModuleName", line: 1}}
           ]

    assert accepts.kind == :accepts
    assert accepts.family == "ActorDefinition"
    assert expands.kind == :expands_with
    assert {:variable, _, "derive_actor"} = expands.expander
  end

  test "a structured macro rejects duplicate family fields" do
    {:ok, tokens} =
      Lexer.tokenize(
        """
        macro Actor
          syntax family Definition
            state Type
            state Type
        """,
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false, prelude_macros: false)

    assert Enum.any?(errors, fn
             {:invalid_macro_family, {:duplicate_syntax_family_field, [{"Definition", "state"}]}, _, _} -> true
             _ -> false
           end)
  end

  test "an open category and qualified category extension are retained" do
    node =
      parse!(
        "macro Reducer\n  open Reducer.ClauseModifier\n  syntax within <d: Duration> is Reducer.ClauseModifier becomes d\n"
      )

    assert {:macro_def, _meta, [open, rule]} = node
    assert open.kind == :open_category
    assert open.name == "Reducer.ClauseModifier"
    assert rule.category == "Reducer.ClauseModifier"
  end

  test "repetition and optional groups are retained as grammar segments" do
    node =
      parse!("""
      macro Grammar
        syntax list <item: Nat>... becomes item
        syntax maybe (<value: Nat>)? becomes value
      """)

    assert {:macro_def, _meta, [repeated, optional]} = node
    assert [{:repeat, {:hole, %{name: "item", kind: "Nat"}}}] = repeated.segments
    assert [{:optional, [{:hole, %{name: "value", kind: "Nat"}}]}] = optional.segments
  end

  test "a delayed raw hole retains its delayed-slot marker" do
    node =
      parse!("macro Lift\n  syntax lift <body: delayed raw until dedent> becomes body\n")

    assert {:macro_def, _meta, [rule]} = node
    assert [{:raw_hole, %{name: "body", delimiter: "dedent", delayed: true}}] = rule.segments
  end

  test "a malformed hole (missing closing `>`) records a :malformed_hole error" do
    {:ok, tokens} =
      Lexer.tokenize("macro Bad\n  syntax every <t: Duration becomes x\n", emit_events: false)

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:malformed_hole, _, _}, &1))
  end

  # `##` doc-comments are ALWAYS emitted by the lexer as `:doc_comment` tokens
  # regardless of `preserve_comments` (see Lexer moduledoc) — unlike plain `#`
  # comments, they are present under default parse options too. The macro
  # container must not mistake one for end-of-block content.
  test "a doc-comment before the first rule does not empty the macro block" do
    node = parse!("macro Foo\n  ## explains the rule\n  syntax now becomes Clock.now()\n")
    assert {:macro_def, _meta, [rule]} = node
    assert rule.keyword == "now"
  end

  test "a doc-comment between two rules does not break parsing" do
    node =
      parse!(
        "macro Foo\n  syntax now becomes Clock.now()\n  ## another rule doc\n  syntax later becomes Clock.later()\n"
      )

    assert {:macro_def, _meta, [rule1, rule2]} = node
    assert rule1.keyword == "now"
    assert rule2.keyword == "later"
  end
end
