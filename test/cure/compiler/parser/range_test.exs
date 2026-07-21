defmodule Cure.Compiler.Parser.RangeTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Parser.Range
  alias Cure.Compiler.Token
  alias Cure.Diagnostic.Span

  test "marks, spans through delimiters, and preserves multiline unicode coordinates" do
    first = token("α", 1, 1, 0, 2, 1, 3)
    last = token("]", 2, 3, 5, 6, 2, 4)

    assert {:ok, marked} = Range.mark(first)
    assert marked.start_byte == 0
    assert marked.end_byte == 2

    assert {:ok, range} = Range.through(first, last)
    assert range.start_byte == 0
    assert range.end_byte == 6
    assert range.end_line == 2
    assert range.end_column == 4
  end

  test "between is half-open and zero_at creates an honest insertion range" do
    first = token("(", 3, 4, 10, 11, 3, 5)
    last = token(")", 3, 7, 14, 15, 3, 8)

    assert {:ok, range} = Range.between(first, last)
    assert range.start_byte == 10 and range.end_byte == 15

    assert {:ok, insertion} = Range.zero_at(last)
    assert insertion.start_byte == 14
    assert insertion.end_byte == 14
    assert insertion.start_line == 3
    assert insertion.end_line == 3
    assert insertion.start_column == 7
    assert insertion.end_column == 7
  end

  test "never merges source identities and rejects missing token spans" do
    left = token("(", 1, 1, 0, 1, 1, 2)
    right = %{token(")", 1, 2, 1, 2, 1, 3) | span: span("other", 1, 2, 1, 2, 1, 3)}

    assert {:error, :different_source} = Range.through(left, right)
    assert {:error, :missing_span} = Range.mark(Token.new(:eof, nil, 1, 1))
  end

  defp token(value, line, column, start_byte, end_byte, end_line, end_column) do
    %Token{
      type: :test,
      value: value,
      line: line,
      col: column,
      span: span("demo.cure", line, column, start_byte, end_byte, end_line, end_column)
    }
  end

  defp span(source, line, column, start_byte, end_byte, end_line, end_column) do
    %Span{
      source_id: source,
      path: source,
      start_byte: start_byte,
      end_byte: end_byte,
      start_line: line,
      start_column: column,
      end_line: end_line,
      end_column: end_column
    }
  end
end
