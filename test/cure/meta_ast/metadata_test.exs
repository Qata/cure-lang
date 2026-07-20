defmodule Cure.MetaAST.MetadataTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Span
  alias Cure.MetaAST.{Metadata, SourceInfo}

  defp span(start_byte, end_byte) do
    %Span{
      source_id: :sentinel,
      path: "sentinel.cure",
      start_byte: start_byte,
      end_byte: end_byte,
      start_line: 1,
      start_column: start_byte + 1,
      end_line: 1,
      end_column: end_byte + 1
    }
  end

  test "canonical source information replaces legacy keys" do
    whole = span(0, 4)
    name = span(0, 2)
    info = %SourceInfo{whole: whole, name: name}

    metadata = Metadata.put_source_info([line: 1, span: whole, name_span: name, semantic: :kept], info)
    assert Keyword.get(metadata, :semantic) == :kept
    assert Keyword.get(metadata, :source_info) == info
    refute Keyword.has_key?(metadata, :span)

    assert Metadata.source_info(span: whole, name_span: name).whole == whole
    assert Metadata.source_info(span: whole, name_span: name).name == name
  end

  test "recursive projection strips metadata stored inside metadata values" do
    source = span(0, 1)

    decorated =
      {:function_def,
       [
         params: [{:param, [type: {:variable, [span: source], "Int"}, span: source], "x"}],
         source_info: %SourceInfo{whole: source}
       ], [{:variable, [span: source], "x"}]}

    plain =
      {:function_def,
       [
         params: [{:param, [type: {:variable, [], "Int"}], "x"}]
       ], [{:variable, [], "x"}]}

    assert Metadata.semantic_equal?(decorated, plain)
    assert Metadata.semantic_key(decorated) == plain
  end
end
