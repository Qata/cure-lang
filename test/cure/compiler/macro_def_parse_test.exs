defmodule Cure.Compiler.MacroDefParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Errors, Lexer, Parser, Printer}
  alias Cure.Diagnostic.Renderer

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

  test "a syntax family records source-defined productions" do
    node =
      parse!("""
      macro Machine
        syntax family Transition
          syntax <from: Name> --<event: Name>--> <to: Name>
        syntax family Definition
          one_or_more transitions Transition
        accepts Definition
        expands with build
      """)

    assert {:macro_def, _, [transition, definition, _, _]} = node
    assert [%{fields: ["from", "event", "to"], segments: segments}] = transition.productions

    assert Enum.map(segments, fn
             {:lit, value} -> value
             {:hole, %{name: name}} -> name
           end) == ["from", "-", "-", "event", "-", "->", "to"]

    assert [%{name: "transitions", shape: "Transition", cardinality: :one_or_more}] = definition.fields
  end

  test "alternative productions may add an optional typed parameter-list capture" do
    node =
      parse!("""
      macro Machine
        syntax family Event
          syntax <name: Name>(<payload: Parameters>)
          syntax <name: Name>
        syntax family Definition
          one_or_more events Event
        accepts Definition
        expands with build
      """)

    assert {:macro_def, _, [_event, _definition, _, _]} = node
    assert :ok = Cure.Compiler.MacroFamily.validate(elem(node, 2))
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

  test "a rule retains ordered obligations on expression captures" do
    node =
      parse!("""
      macro Child
        syntax child <identity: Expression> where BeamEncode(identity) where Equatable(identity) computed directly by build_child
      """)

    assert {:macro_def, _, [rule]} = node

    assert Enum.map(rule.obligations, &{&1.interface, &1.capture}) == [
             {"BeamEncode", "identity"},
             {"Equatable", "identity"}
           ]
  end

  test "a family field retains obligations on its semantic capture" do
    node =
      parse!("""
      macro Supervisor
        syntax family ChildDefinition
          id Expression where BeamEncode(id)
      """)

    assert {:macro_def, _, [%{fields: [field]}]} = node
    assert [%{interface: "BeamEncode", capture: "id"}] = field.obligations
  end

  test "an obligation must name a capture owned by its rule" do
    source =
      "macro Bad\n  syntax child <identity: Expression> where BeamEncode(identitty) becomes identity\n"

    {:ok, tokens} =
      Lexer.tokenize(
        source,
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false, prelude_macros: false)
    assert [{:unknown_macro_obligation_capture, details} = error] = errors
    assert details.capture == "identitty"
    assert details.span.start_line == 2
    assert details.span.start_column == 56
    assert details.span.end_column == 65

    {diagnostic, registry} = Errors.to_diagnostic({:parse_error, [error]}, "obligation.cure", source)
    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- UNKNOWN MACRO CAPTURE [E092] -------------------------------- obligation.cure

             The `BeamEncode` obligation refers to `identitty`, but this rule declares no
             capture with that name.

             at obligation.cure:2:56
             2 | …ession> where BeamEncode(identitty) becomes identity
               |                           ^^^^^^^^^ this capture is not declared by the rule

             Hint: Replace it with the declared capture `identity`
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "identity"}]}] =
             diagnostic.suggestions

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 1, "character" => 55},
             "end" => %{"line" => 1, "character" => 64}
           }
  end

  test "capture obligations survive printing and reparsing" do
    source = """
    macro Child
      syntax family Definition
        id Expression where BeamEncode(id)
      syntax child <id: Expression> where BeamEncode(id) becomes id
    """

    printed = source |> parse!() |> Printer.quoted_to_string()
    assert printed =~ "id Expression where BeamEncode(id)"
    assert printed =~ "<id: Expression> where BeamEncode(id)"
    assert {:macro_def, _, [family, rule]} = parse!(printed)
    assert hd(family.fields).obligations != []
    assert rule.obligations != []
  end

  test "a family may include another family" do
    node =
      parse!("""
      macro Service <name: ModuleName>
        syntax family Common
          state Type
        syntax family ServiceDefinition
          includes Common
          optional timeout Int
        accepts ServiceDefinition
        expands with derive_service
      """)

    assert {:macro_def, _meta, [common, family, accepts, expands]} = node
    assert common.name == "Common"
    assert family.includes == [{"Common", 5, 5}]
    assert accepts.family == "ServiceDefinition"
    assert {:variable, _, "derive_service"} = expands.expander
  end

  test "family composition rejects unknown included families" do
    {:ok, tokens} =
      Lexer.tokenize(
        """
        macro Bad
          syntax family Service
            includes Missing
            state Type
          accepts Service
          expands with build
        """,
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert Enum.any?(errors, fn
             {:invalid_macro_family, {:unknown_syntax_family, "Missing"}, _, _} -> true
             _ -> false
           end)
  end

  test "family composition rejects cycles" do
    {:ok, tokens} =
      Lexer.tokenize(
        """
        macro Bad
          syntax family First
            includes Second
          syntax family Second
            includes First
          accepts First
          expands with build
        """,
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert Enum.any?(errors, fn
             {:invalid_macro_family, {:syntax_family_cycle, ["First", "Second", "First"]}, _, _} -> true
             _ -> false
           end)
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
    assert Enum.any?(errors, &match?({:malformed_hole, %{observed: "becomes"}}, &1))
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
