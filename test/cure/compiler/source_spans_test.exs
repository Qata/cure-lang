defmodule Cure.Compiler.SourceSpansTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, SourceSpans}
  alias Cure.Diagnostic.Span
  alias Cure.Elab.MacroExpand
  alias Cure.MetaAST.Metadata

  test "parser metadata retains complete authored construct and focused name spans" do
    source = "mod Demo\n  fn answer(x: Int) -> Int = helper(x)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    spans = collect_spans(ast)
    assert spans != []
    assert Enum.all?(spans, &match?(%Span{source_id: "demo.cure"}, &1))

    function = find_node(ast, :function_def)
    function_span = function |> elem(1) |> Metadata.source_info() |> Map.fetch!(:whole)
    assert slice(source, function_span) =~ "fn answer"
    assert slice(source, function_span) =~ "helper(x)"
    assert slice(source, Metadata.source_info(elem(function, 1)).name) == "answer"

    [{:param, parameter_meta, "x"}] = Keyword.fetch!(elem(function, 1), :params)
    parameter_info = Metadata.source_info(parameter_meta)
    assert slice(source, parameter_info.whole) == "x: Int"
    assert slice(source, parameter_info.name) == "x"

    call = find_node(ast, :function_call)
    call_meta = elem(call, 1)
    call_info = Metadata.source_info(call_meta)
    assert call_info.callee != nil
    assert length(call_info.arguments) == 1
    assert slice(source, call_info.callee) == "helper"
    assert slice(source, call_info.whole) == "helper(x)"
    assert Enum.map(call_info.arguments, &slice(source, &1)) == ["x"]
    assert Enum.all?(elem(call, 2), fn child -> match?({_, meta, _} when is_list(meta), child) end)
  end

  test "annotations stored in declaration metadata retain their authored spans" do
    source = "mod Demo\n  fn answer(x: Int) -> Int = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    {:function_def, meta, _body} = find_node(ast, :function_def)
    function_info = Metadata.source_info(meta)
    {:variable, return_meta, "Int"} = Keyword.fetch!(meta, :return_type)
    [{:param, parameter_meta, "x"}] = Keyword.fetch!(meta, :params)
    {:variable, parameter_type_meta, "Int"} = Keyword.fetch!(parameter_meta, :type)

    assert slice(source, Metadata.source_info(return_meta).whole) == "Int"
    assert slice(source, Metadata.source_info(parameter_type_meta).whole) == "Int"
    assert slice(source, function_info.annotation) == "Int"
  end

  test "parameter source info owns the authored annotation range" do
    source = "fn answer({value: Int}, count :linear Nat) -> Int = count\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "params.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "params.cure", emit_events: false, prelude_macros: false)

    {:function_def, meta, _body} = find_node(ast, :function_def)
    [{:param, implicit_meta, "value"}, {:param, explicit_meta, "count"}] = Keyword.fetch!(meta, :params)

    assert slice(source, Metadata.source_info(implicit_meta).annotation) == ": Int"
    assert slice(source, Metadata.source_info(explicit_meta).annotation) == ":linear Nat"
  end

  test "let bindings retain their authored whole, name, and annotation ranges" do
    source = "fn answer() -> Int = let value: Int = 1\n  value\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "let.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "let.cure", emit_events: false, prelude_macros: false)

    assignment = find_node(ast, :assignment)
    info = Metadata.source_info(elem(assignment, 1))

    assert slice(source, info.whole) == "let value: Int = 1"
    assert slice(source, info.name) == "value"
    assert slice(source, info.annotation) == ": Int"
  end

  test "macro declarations retain the authored container and macro name ranges" do
    source = "macro Every\n  syntax every becomes Clock.now()\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro.cure", emit_events: false)

    assert {:ok, {:macro_def, meta, [rule]}} =
             Parser.parse(tokens, file: "macro.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "macro Every\n  syntax every becomes Clock.now()"
    assert slice(source, info.name) == "Every"
    assert slice(source, rule.source_span) == "syntax every becomes Clock.now()"
  end

  test "structured macro sections retain authored entry ranges" do
    source =
      "macro actor <name: ModuleName>\n" <>
        "  syntax family ActorDefinition\n" <>
        "    syntax actor <name: ModuleName>\n" <>
        "    state Type\n" <>
        "  accepts ActorDefinition\n" <>
        "  expands with derive_actor\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro_sections.cure", emit_events: false)

    assert {:ok, {:macro_def, _meta, [family, accepts, expands]}} =
             Parser.parse(tokens, file: "macro_sections.cure", emit_events: false, prelude_macros: false)

    assert slice(source, family.source_span) ==
             "syntax family ActorDefinition\n    syntax actor <name: ModuleName>\n    state Type"

    assert slice(source, accepts.source_span) == "accepts ActorDefinition"
    assert slice(source, expands.source_span) == "expands with derive_actor"
    assert [field] = family.fields
    assert slice(source, field.source_span) == "state Type"
    assert [production] = family.productions
    assert slice(source, production.source_span) == "syntax actor <name: ModuleName>"
  end

  test "macro failure and explanation sections retain authored ranges" do
    source =
      "macro Protocol\n" <>
        "  fail ReplyBeforeRequest(state: Code)\n" <>
        "  explain\n" <>
        "    ReplyBeforeRequest => \"a reply needs an open request\"\n" <>
        "  open Category\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro_diagnosis.cure", emit_events: false)

    assert {:ok, {:macro_def, _meta, [failure, explanation, open]}} =
             Parser.parse(tokens, file: "macro_diagnosis.cure", emit_events: false, prelude_macros: false)

    assert slice(source, failure.source_span) == "fail ReplyBeforeRequest(state: Code)"
    assert slice(source, explanation.source_span) =~ "explain\n    ReplyBeforeRequest"
    [clause] = explanation.clauses
    assert slice(source, clause.source_span) == "ReplyBeforeRequest => \"a reply needs an open request\""
    assert slice(source, open.source_span) == "open Category"
  end

  test "macro examples retain their authored range" do
    source =
      "macro Every\n" <>
        "  syntax every <t: Duration> becomes Timer.repeat(t)\n" <>
        "    example every 500 expands Timer.repeat(500)\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro_example.cure", emit_events: false)

    assert {:ok, {:macro_def, _meta, [rule]}} =
             Parser.parse(tokens, file: "macro_example.cure", emit_events: false, prelude_macros: false)

    [example] = rule.examples
    assert slice(source, example.source_span) == "example every 500 expands Timer.repeat(500)"
  end

  test "named containers retain exact declaration and qualified-name ranges" do
    source = "mod Demo.Core\n  rec Point\n    x: Int\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "containers.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "containers.cure", emit_events: false, prelude_macros: false)

    {:container, module_meta, [record]} = ast
    {:container, record_meta, _fields} = record

    module_info = Metadata.source_info(module_meta)
    record_info = Metadata.source_info(record_meta)
    assert slice(source, module_info.whole) == "mod Demo.Core\n  rec Point\n    x: Int"
    assert slice(source, module_info.name) == "Demo.Core"
    assert slice(source, record_info.whole) == "rec Point\n    x: Int"
    assert slice(source, record_info.name) == "Point"
  end

  test "type declarations and aliases retain exact declaration and name ranges" do
    source = "typealias UserId = Int\ntype Color = Red | Blue deriving Show\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "types.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "types.cure", emit_events: false, prelude_macros: false)

    {:block, _, [alias, enum]} = ast
    alias_info = Metadata.source_info(elem(alias, 1))
    enum_info = Metadata.source_info(elem(enum, 1))

    assert slice(source, alias_info.whole) == "typealias UserId = Int"
    assert slice(source, alias_info.name) == "UserId"
    assert slice(source, enum_info.whole) == "type Color = Red | Blue deriving Show"
    assert slice(source, enum_info.name) == "Color"
  end

  test "ADT variants retain exact constructor names and extents" do
    source = "type Maybe = None | Some(Int)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "variants.cure", emit_events: false)

    assert {:ok, {:container, _meta, [none, some]}} =
             Parser.parse(tokens, file: "variants.cure", emit_events: false, prelude_macros: false)

    {:variable, none_meta, "None"} = none
    {:function_def, some_meta, []} = some
    none_info = Metadata.source_info(none_meta)
    some_info = Metadata.source_info(some_meta)

    assert slice(source, none_info.name) == "None"
    assert slice(source, none_info.whole) == "None"
    assert slice(source, some_info.name) == "Some"
    assert slice(source, some_info.whole) == "Some(Int)"
  end

  test "imports and fixity declarations retain authored source roles" do
    source = "use Std.List as L\nprecedencegroup additive\ninfix <+> : additive\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "declarations.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "declarations.cure", emit_events: false, prelude_macros: false)

    import = find_node(ast, :import)
    group = find_node(ast, :precedencegroup)
    fixity = find_node(ast, :fixity)
    import_info = Metadata.source_info(elem(import, 1))
    group_info = Metadata.source_info(elem(group, 1))
    fixity_info = Metadata.source_info(elem(fixity, 1))

    assert slice(source, import_info.whole) == "use Std.List as L"
    assert slice(source, import_info.name) == "Std.List"
    assert slice(source, group_info.whole) == "precedencegroup additive"
    assert slice(source, group_info.name) == "additive"
    assert slice(source, fixity_info.whole) == "infix <+> : additive"
    assert slice(source, fixity_info.operator) == "<+>"
  end

  test "protocol and interface declarations retain authored name ranges" do
    source = "proto Show(T)\n  fn show(x: T) -> String\ninterface Eq(T)\n  fn eq(x: T, y: T) -> Bool\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "traits.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "traits.cure", emit_events: false, prelude_macros: false)

    proto = find_node(ast, :container)
    interface = find_node(ast, :interface)
    proto_info = Metadata.source_info(elem(proto, 1))
    interface_info = Metadata.source_info(elem(interface, 1))

    assert slice(source, proto_info.whole) == "proto Show(T)\n  fn show(x: T) -> String"
    assert slice(source, proto_info.name) == "Show"
    assert slice(source, interface_info.whole) == "interface Eq(T)\n  fn eq(x: T, y: T) -> Bool"
    assert slice(source, interface_info.name) == "Eq"
  end

  test "record declaration fields retain authored parameter ranges" do
    source = "rec Point\n  x: Int = 0\n  y: String\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "record_decl.cure", emit_events: false)

    assert {:ok, {:container, _meta, fields}} =
             Parser.parse(tokens, file: "record_decl.cure", emit_events: false, prelude_macros: false)

    [{:param, x_meta, "x"}, {:param, y_meta, "y"}] = fields
    assert slice(source, Metadata.source_info(x_meta).whole) == "x: Int = 0"
    assert slice(source, Metadata.source_info(x_meta).name) == "x"
    assert slice(source, Metadata.source_info(x_meta).annotation) == ": Int"
    assert slice(source, Metadata.source_info(y_meta).whole) == "y: String"
  end

  test "type applications in annotations retain their closing delimiter" do
    source = "mod Demo\n  fn answer(x: Option(Int)) -> Option(Int) = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    {:function_def, meta, _body} = find_node(ast, :function_def)
    {:function_call, return_meta, _} = Keyword.fetch!(meta, :return_type)
    [{:param, parameter_meta, "x"}] = Keyword.fetch!(meta, :params)
    {:function_call, parameter_type_meta, _} = Keyword.fetch!(parameter_meta, :type)

    assert slice(source, Metadata.source_info(return_meta).whole) == "Option(Int)"
    assert slice(source, Metadata.source_info(parameter_type_meta).whole) == "Option(Int)"
  end

  test "match arms retain parser-owned pattern, guard, body, and whole spans" do
    source = "fn choose(x: Int) -> Int = match x\n  n when n > 0 -> n\n  _ -> 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "match.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "match.cure", emit_events: false, prelude_macros: false)

    {:match_arm, arm_meta, _} = find_node(ast, :match_arm)
    info = Metadata.source_info(arm_meta)

    assert slice(source, info.whole) == "n when n > 0 -> n"
    assert slice(source, info.pattern) == "n"
    assert slice(source, info.guard) == "n > 0"
    assert slice(source, info.body) == "n"
  end

  test "match expressions retain their whole and branch-owned spans" do
    source = "fn choose(x: Int) -> Int = match x\n  n -> n\n  _ -> 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "match.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "match.cure", emit_events: false, prelude_macros: false)

    {:pattern_match, meta, _} = find_node(ast, :pattern_match)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "match x\n  n -> n\n  _ -> 0"
    assert Enum.map(info.branches, &slice(source, &1)) == ["n -> n", "_ -> 0"]
  end

  test "conditionals retain condition and branch-owned spans" do
    source = "fn choose(x: Int) -> Int = if x > 0 then x else 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "conditional.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "conditional.cure", emit_events: false, prelude_macros: false)

    {:conditional, meta, _} = find_node(ast, :conditional)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "if x > 0 then x else 0"
    assert slice(source, info.condition) == "x > 0"
    assert slice(source, info.then_branch) == "x"
    assert slice(source, info.else_branch) == "0"
  end

  test "single-scrutinee with expressions retain whole and branch spans" do
    source = "fn choose(x: Int) -> Int = with x\n  n -> n\n  _ -> 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "with.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "with.cure", emit_events: false, prelude_macros: false)

    {:with_abs, meta, _} = find_node(ast, :with_abs)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "with x\n  n -> n\n  _ -> 0"
    assert Enum.map(info.branches, &slice(source, &1)) == ["n -> n", "_ -> 0"]
  end

  test "multi-scrutinee with preserves the outer authored range" do
    source = "fn choose(a: Int, b: Int) -> Int = with a b\n  x, y -> x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "with_multi.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "with_multi.cure", emit_events: false, prelude_macros: false)

    {:with_abs, meta, _} = find_node(ast, :with_abs)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "with a b\n  x, y -> x"
    assert Enum.map(info.branches, &slice(source, &1)) == ["x"]
  end

  test "record constructions retain authored name, delimiters, and field spans" do
    source = "fn origin() -> Point = Point{x: 0, y: 0}\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "record.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "record.cure", emit_events: false, prelude_macros: false)

    {:function_call, meta, _fields} = find_node(ast, :function_call)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "Point{x: 0, y: 0}"
    assert slice(source, info.name) == "Point"
    assert slice(source, info.opener) == "{"
    assert slice(source, info.closer) == "}"
    assert slice(source, Map.fetch!(info.fields, :x)) == "x"
    assert slice(source, Map.fetch!(info.fields, :y)) == "y"
  end

  test "operators and containers retain token-owned focused ranges" do
    source =
      "mod Demo\n  fn answer() -> Int = 1 + 2\n  fn xs() -> List(Int) = [1, 2]\n  fn pair() -> Tuple(Int, Int) = %[1, 2]\n" <>
        "  fn fields() = %{x: 1}\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    binary = find_node(ast, :binary_op)
    binary_info = Metadata.source_info(elem(binary, 1))
    assert slice(source, binary_info.operator) == "+"
    assert Enum.map(binary_info.operands, &slice(source, &1)) == ["1", "2"]

    for {tag, expected} <- [
          {:list, "[1, 2]"},
          {:tuple, "%[1, 2]"},
          {:map, "%{x: 1}"}
        ] do
      node = find_node(ast, tag)
      info = Metadata.source_info(elem(node, 1))
      assert slice(source, info.whole) == expected

      expected_opener =
        case tag do
          :tuple -> "%["
          :map -> "%{"
          :list -> "["
        end

      assert slice(source, info.opener) == expected_opener
      assert slice(source, info.closer) == String.last(expected)
    end
  end

  test "string interpolation retains its whole and embedded expression ranges" do
    source = ~S|fn message(name: String) -> String = "hello #{name}! #{name + 1}"| <> "\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "interpolation.cure", emit_events: false)

    assert {:ok, ast} =
             Parser.parse(tokens, file: "interpolation.cure", emit_events: false, prelude_macros: false)

    interpolation = find_node(ast, :string_interpolation)
    info = Metadata.source_info(elem(interpolation, 1))

    assert slice(source, info.whole) == ~S|"hello #{name}! #{name + 1}"|
    assert Enum.map(info.arguments, &slice(source, &1)) == ["name", "name + 1"]
  end

  test "diagnostic metadata is excluded from semantic comparisons" do
    span = %Span{
      source_id: :one,
      path: "one.cure",
      start_byte: 0,
      end_byte: 1,
      start_line: 1,
      start_column: 1,
      end_line: 1,
      end_column: 2
    }

    plain = {:variable, [line: 1, col: 1, scope: :local], "x"}
    located = {:variable, [line: 1, col: 1, scope: :local, span: span, construct_span: span], "x"}

    assert SourceSpans.strip_diagnostic_meta(plain) == SourceSpans.strip_diagnostic_meta(located)
    refute MacroExpand.contains_computed_use?(located)
  end

  defp collect_spans({_, meta, payload}) when is_list(meta) do
    own =
      case Metadata.source_info(meta) do
        %{whole: %Span{} = span} -> [span]
        _ -> []
      end

    own ++ collect_spans(payload)
  end

  defp collect_spans(list) when is_list(list), do: Enum.flat_map(list, &collect_spans/1)
  defp collect_spans(tuple) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> Enum.flat_map(&collect_spans/1)
  defp collect_spans(_), do: []

  defp find_node({node_tag, _, _} = node, wanted_tag) when node_tag == wanted_tag, do: node

  defp find_node({_, _, payload}, tag), do: find_node(payload, tag)

  defp find_node(list, tag) when is_list(list) do
    Enum.find_value(list, &find_node(&1, tag))
  end

  defp find_node(tuple, tag) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> find_node(tag)
  defp find_node(_, _), do: nil

  defp slice(source, span), do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)
end
