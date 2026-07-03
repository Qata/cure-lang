defmodule Cure.Elab.LiteralPatternTest do
  @moduledoc """
  Literal patterns on a primitive scrutinee (Int/Bool/Float) desugar to a chain
  of `bool_elim` — there is no inductive `:vdata` to dispatch on. `match n | 0 ->
  a | _ -> b` becomes `bool_elim (n == 0) a b`; `match b | true -> t | false -> f`
  becomes `bool_elim b t f`. Built on the committed `bool_elim` primitive + the
  existing `{:prim, :eq}`; no kernel change.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "integer literal pattern with a catch-all runs on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    0 -> Z()\n" <>
        "    1 -> S(Z())\n" <>
        "    m -> S(S(Z()))\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\n" <>
        "  fn c() -> Nat = classify(9)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Lit1", functions: [:classify, :a, :b, :c])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
    assert apply(mod, :c, []) == {:S, {:S, :Z}}
  end

  test "boolean literal pattern (exhaustive, no catch-all) runs on the BEAM" do
    src =
      @nat <>
        "  fn toNat(b: Bool) -> Nat = match b\n    true -> S(Z())\n    false -> Z()\n" <>
        "  fn t() -> Nat = toNat(true)\n  fn f() -> Nat = toNat(false)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Lit2", functions: [:toNat, :t, :f])

    assert apply(mod, :t, []) == {:S, :Z}
    assert apply(mod, :f, []) == :Z
  end

  test "a named catch-all binds the scrutinee" do
    src =
      @nat <>
        "  fn pred(n: Int) -> Int = match n\n    0 -> 0\n    m -> m\n" <>
        "  fn z() -> Int = pred(0)\n  fn nz() -> Int = pred(7)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Lit3", functions: [:pred, :z, :nz])

    assert apply(mod, :z, []) == 0
    assert apply(mod, :nz, []) == 7
  end
end
