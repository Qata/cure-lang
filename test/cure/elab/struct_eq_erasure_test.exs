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
end
