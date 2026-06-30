defmodule Cure.Elab.IndexedTypeParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    ast
  end

  test "parses an indexed type declaration with constructor signatures" do
    src = """
    indexed type SF(as: SVDesc, bs: SVDesc, d: Dec) where
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, and(d1, d2))
    """

    assert {:indexed_type, meta, ctors} = parse(src)
    assert Keyword.get(meta, :name) == "SF"
    assert length(Keyword.get(meta, :index_params)) == 3
    assert [{:gadt_ctor, m1, t1}, {:gadt_ctor, m2, t2}] = ctors
    assert Keyword.get(m1, :name) == "prim"
    assert Keyword.get(m2, :name) == "seq"

    # prim: a single-element chain; the SF head is preserved (not mangled).
    assert {:arrow_chain, [{:function_call, [name: "SF"], _}]} = t1

    # seq: two domains + a result, every SF application head intact, and the
    # computed result index `and(d1, d2)` preserved as a nested application.
    assert {:arrow_chain, [dom1, dom2, result]} = t2
    assert {:function_call, [name: "SF"], _} = dom1
    assert {:function_call, [name: "SF"], _} = dom2
    assert {:function_call, [name: "SF"], [_, _, {:function_call, [name: "and"], [_, _]}]} = result
  end
end
