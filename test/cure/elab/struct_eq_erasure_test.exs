defmodule Cure.Elab.StructEqErasureTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # `==` on an abstract type variable lowers to the polymorphic `struct_eq`, whose
  # type argument is computationally irrelevant (dropped at emit). It must be
  # ERASED, so passing the enclosing function's erased type parameter into it is
  # not a relevance violation (#26 — `Std.List.contains` used to fail here).
  test "== on an abstract type parameter elaborates (erased type arg) and runs" do
    src = """
    mod SE
      fn has(x: t, y: t) -> Bool = x == y
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.SE", functions: [:has])

    assert apply(m, :has, [3, 3]) == true
    assert apply(m, :has, [3, 4]) == false
  end

  # `==` on a value of an INDEXED family (`Bounded(n)` — Char's underlying type)
  # also lowers to `struct_eq`, whose reified type argument is the applied family
  # `Bounded(n)`. That reification MUST carry the signature so the index `n` is
  # filed as an index and not a parameter; otherwise the kernel's params/indices
  # split arity-checks a 1-arg spine against Bounded's 0-param telescope and
  # rejects with `:arg_arity`. Nullary families (`Nat`) never hit this because
  # they have no arg to misfile. Bounded erases to a native int, so `==` runs as
  # BEAM integer equality.
  test "== on an indexed family (Bounded) elaborates and runs — index not misfiled as a param" do
    src = """
    mod SE
      use Std.Bounded
      fn eqb(x: Bounded(10), y: Bounded(10)) -> Bool = x == y
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.SE", functions: [:eqb])

    assert apply(m, :eqb, [3, 3]) == true
    assert apply(m, :eqb, [3, 4]) == false
  end
end
