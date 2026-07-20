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

    call = find_node(ast, :function_call)
    call_meta = elem(call, 1)
    call_info = Metadata.source_info(call_meta)
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
    {:variable, return_meta, "Int"} = Keyword.fetch!(meta, :return_type)
    [{:param, parameter_meta, "x"}] = Keyword.fetch!(meta, :params)
    {:variable, parameter_type_meta, "Int"} = Keyword.fetch!(parameter_meta, :type)

    assert slice(source, Metadata.source_info(return_meta).whole) == "Int"
    assert slice(source, Metadata.source_info(parameter_type_meta).whole) == "Int"
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
