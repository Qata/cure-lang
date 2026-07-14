defmodule Cure.Compiler.BinaryComprehensionTest do
  @moduledoc """
  Tests for the v0.22.0 binary comprehension generator surface:

      [body for <<pattern <- source>>]

  The parser emits a `:binary_generator` qualifier node that the codegen
  lowers to Erlang's `b_generate` qualifier inside the existing `:lc`
  comprehension form.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  describe "parser" do
    test "emits :binary_generator qualifier with a :bytes pattern" do
      ast = parse!("[b for <<b <- buf>>]")
      assert {:comprehension, _, [_body | qs]} = ast
      assert [{:binary_generator, _, [pattern, source]}] = qs
      assert {:literal, meta, [_seg]} = pattern
      assert Keyword.get(meta, :subtype) == :bytes
      assert match?({:variable, _, "buf"}, source)
    end

    test "accepts a segment specifier" do
      ast = parse!("[w for <<w::16 <- buf>>]")
      {:comprehension, _, [_ | [{:binary_generator, _, [pattern, _]}]]} = ast
      {:literal, _, [{:bin_segment, seg_meta, _}]} = pattern
      assert Keyword.get(seg_meta, :size) != nil
    end

    test "ordinary list generators still parse" do
      ast = parse!("[x for x <- [1, 2, 3]]")
      assert {:comprehension, _, [_ | [{:generator, _, _}]]} = ast
    end
  end

  test "byte generators compile and evaluate through the stdlib byte view" do
    source = """
    mod BinaryComprehensionTest
      use Std.List
      fn bytes(buf: Binary) -> List(Int) = [b for <<b <- buf>>]
      fn sum(buf: Binary) -> Int = Std.List.foldl(bytes(buf), 0, fn(b) -> fn(acc) -> acc + b)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :bytes, [<<1, 2, 3>>]) == [1, 2, 3]
    assert apply(module, :sum, [<<1, 2, 3, 4>>]) == 10
  end
end
