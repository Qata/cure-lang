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
    assert [{:gadt_ctor, m1, _t1}, {:gadt_ctor, m2, t2}] = ctors
    assert Keyword.get(m1, :name) == "prim"
    assert Keyword.get(m2, :name) == "seq"
    # seq's signature is a function-type chain (its arrows produce a Function type)
    assert {:function_call, fmeta, _args} = t2
    assert Keyword.get(fmeta, :function_type) == true
  end
end
