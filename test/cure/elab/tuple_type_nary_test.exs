defmodule Cure.Elab.TupleTypeNaryTest do
  # `Tuple(T1, …, Tn)` for n ≥ 3 is the honest n-ary surface tuple type. It parses
  # to `{:tuple_type, [arity: n], [t1…tn]}` (a flat product), distinct from the
  # arity-2 `Tuple(T, U)` which keeps aliasing the non-dependent `Sigma`
  # (`{:sigma_type, …}`, Task 1). The elaborator lowers `{:tuple_type, …}` to the
  # per-arity `TupleN` inductive family (Task 4); at parse time it is only a shape.
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Collect every `{tag, _, _}` node anywhere in the AST — descending through
  # BOTH children and meta (a fn's return type lives in the def's meta).
  defp nodes_of({tag, _, _} = n, tag), do: [n | deep(Tuple.to_list(n), tag)]
  defp nodes_of(t, tag) when is_tuple(t), do: deep(Tuple.to_list(t), tag)
  defp nodes_of(list, tag) when is_list(list), do: deep(list, tag)
  defp nodes_of(_other, _tag), do: []

  defp deep(elems, tag) when is_list(elems), do: Enum.flat_map(elems, &nodes_of(&1, tag))

  test "Tuple(Int, Int, Int) parses to {:tuple_type, arity: 3, [_,_,_]}" do
    ast = parse("""
    mod M
      fn mk(a: Int, b: Int, c: Int) -> Tuple(Int, Int, Int) = a
    """)

    assert [{:tuple_type, meta, elems}] = nodes_of(ast, :tuple_type)
    assert Keyword.get(meta, :arity) == 3
    assert length(elems) == 3
  end

  test "arity-2 Tuple(Int, Int) still aliases Sigma — no tuple_type node" do
    ast = parse("""
    mod M
      fn mk(a: Int, b: Int) -> Tuple(Int, Int) = a
    """)

    assert nodes_of(ast, :tuple_type) == []
    assert [{:sigma_type, _, [_, _]} | _] = nodes_of(ast, :sigma_type)
  end
end
