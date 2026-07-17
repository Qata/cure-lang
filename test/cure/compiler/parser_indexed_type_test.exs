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

  # The chain of a constructor signature: the list of type atoms inside its
  # `{:arrow_chain, atoms}`, keyed by constructor name.
  defp ctor_chain(ast, ctor_name) do
    collect(ast, [])
    |> Enum.find_value(fn
      {:gadt_ctor, meta, {:arrow_chain, atoms}} ->
        if Keyword.get(meta, :name) == ctor_name, do: atoms, else: nil

      _ ->
        nil
    end)
  end

  test "named dependent ctor arg `(k: Nat)` retains its binder in the arrow chain" do
    src = """
    mod M
      type NVv indices (n: Nat)
        vz : NVv(Z)
        vc : (k: Nat) -> SNat(k) -> NVv(S(k))
    """

    {:ok, ast} = parse_decl(src)
    chain = ctor_chain(ast, "vc")

    # First atom is the NAMED binder `(k: Nat)`; its name is retained and its
    # type is the ordinary `Nat` type atom.
    assert [first, second, result] = chain
    assert {:named_dom, "k", {:variable, [scope: :local], "Nat"}} = first

    # A later argument type resolves the bound `k` as a plain variable, and the
    # result index `NVv(S(k))` likewise references it — proving the binder is in
    # scope for subsequent atoms.
    assert {:function_call, [name: "SNat"], [{:variable, [scope: :local], "k"}]} = second

    assert {:function_call, [name: "NVv"], [{:function_call, [name: "S"], [{:variable, [scope: :local], "k"}]}]} =
             result
  end

  test "unnamed ctor arg types are unchanged (no :named_dom wrapper)" do
    src = """
    mod M
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
    """

    {:ok, ast} = parse_decl(src)
    chain = ctor_chain(ast, "ssuc")

    # Both atoms are bare type applications — the pre-existing shape, byte-for-byte.
    assert [{:function_call, [name: "SNat"], _}, {:function_call, [name: "SNat"], _}] = chain
    refute Enum.any?(chain, &match?({:named_dom, _, _}, &1))
  end

  test "higher-order ctor fields share the dependent-arrow grammar" do
    src = """
    mod M
      type Acc(a: Type) indices (xs: List(a))
        MkAcc : (descend: ((ys: List(a)) -> Smaller(a, ys, xs) -> Acc(a, ys))) -> Acc(a, xs)
    """

    {:ok, ast} = parse_decl(src)
    [field, _result] = ctor_chain(ast, "MkAcc")

    assert {:named_dom, "descend", {:pi_type, [binders: ["ys", nil]], [ys_type, smaller, acc]}} = field
    assert {:function_call, [name: "List"], _} = ys_type
    assert {:function_call, [name: "Smaller"], _} = smaller
    assert {:function_call, [name: "Acc"], _} = acc
  end
end
