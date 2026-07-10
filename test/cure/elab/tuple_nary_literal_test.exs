defmodule Cure.Elab.TupleNaryLiteralTest do
  # `%[a1,…,an]` for 3 ≤ n ≤ 8 elaborates to the flat per-arity `TupleN` family and
  # emits a flat BEAM tuple `{a1,…,an}` — the honest n-ary product (Haskell/OCaml
  # bounded tuples). A NESTED pair `%[a, %[b, c]]` stays `mk_tuple2(a, mk_tuple2(b,c))`
  # → `{a, {b, c}}`, distinct from the flat 3-tuple: the representation distinctness
  # is preserved without a kernel change (they are different inductive families).
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "%[1,2,3] : Tuple(Int,Int,Int) elaborates and emits a flat 3-tuple" do
    src = """
    mod M
      fn mk() -> Tuple(Int, Int, Int) = %[1, 2, 3]
    """
    assert {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:mk])
    assert apply(m, :mk, []) == {1, 2, 3}
  end

  test "an 8-tuple emits flat" do
    src = """
    mod M
      fn mk() -> Tuple(Int, Int, Int, Int, Int, Int, Int, Int) = %[1, 2, 3, 4, 5, 6, 7, 8]
    """
    assert {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:mk])
    assert apply(m, :mk, []) == {1, 2, 3, 4, 5, 6, 7, 8}
  end

  test "a nested pair stays distinct from a flat 3-tuple" do
    src = """
    mod M
      fn mk() -> Tuple(Int, Tuple(Int, Int)) = %[1, %[2, 3]]
    """
    assert {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:mk])
    assert apply(m, :mk, []) == {1, {2, 3}}
  end

  test "arity > 8 is rejected" do
    src = """
    mod M
      fn mk() -> Int = %[1, 2, 3, 4, 5, 6, 7, 8, 9]
    """
    assert {:error, {:tuple_arity_exceeded, 9}} = Program.elaborate(src)
  end
end
