defmodule Cure.Compiler.ParserIndexedTypeTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse_decl(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(toks, emit_events: false)
  end

  # Collect every {tag, meta, children} 3-tuple in the AST.
  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  defp find_indexed_type(ast, name) do
    collect(ast, [])
    |> Enum.find(fn
      {:indexed_type, meta, _} -> Keyword.get(meta, :name) == name
      _ -> false
    end)
  end

  defp find_type(ast, name) do
    collect(ast, [])
    |> Enum.find(fn
      {tag, meta, _} when tag in [:indexed_type, :container, :type_annotation] ->
        Keyword.get(meta, :name) == name

      _ ->
        false
    end)
  end

  test "type NAME(params) indices (idx) parses into split meta" do
    src = """
    mod M
      type Vector(a: Type) indices (n: Nat)
        empty   : Vector(a, Z)
        prepend : a -> Vector(a, n) -> Vector(a, S(n))
    """

    {:ok, ast} = parse_decl(src)
    node = find_indexed_type(ast, "Vector")
    assert {:indexed_type, meta, ctors} = node
    assert Keyword.get(meta, :params) |> length() == 1
    assert Keyword.get(meta, :indices) |> length() == 1
    assert length(ctors) == 2
  end

  test "parameter-free family: type Length indices (n: Nat)" do
    src = "mod M\n  type Length indices (n: Nat)\n    zero : Length(Z)\n"
    {:ok, ast} = parse_decl(src)
    assert {:indexed_type, meta, _} = find_indexed_type(ast, "Length")
    assert Keyword.get(meta, :params) == []
    assert Keyword.get(meta, :indices) |> length() == 1
  end

  test "ordinary ADT still parses unchanged" do
    src = "mod M\n  type Option(a) = Some(a) | None\n"
    {:ok, ast} = parse_decl(src)
    refute match?({:indexed_type, _, _}, find_type(ast, "Option"))
  end
end
