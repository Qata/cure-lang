defmodule Cure.Elab.GuardTest do
  @moduledoc """
  Boolean `when` guards on a variable/catch-all pattern desugar to a chain of
  `bool_elim`: `match n | x when g -> a | x -> b` becomes `bool_elim g a b`,
  with each guard test its own Boolean elimination and the final unguarded
  catch-all closing the chain (the fall-through when every guard is false).

  Guards need surface comparison operators to elaborate, so `{:binary_op}` now
  lowers to the kernel's `{:prim, op, …}` (e.g. `x == 0` -> `{:prim, :eq, …}`).
  Both build on the committed `bool_elim` primitive; no kernel change.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a surface comparison operator elaborates and runs on the BEAM" do
    src =
      "mod M\n" <>
        "  fn eq0(n: Int) -> Bool = n == 0\n" <>
        "  fn t() -> Bool = eq0(0)\n  fn f() -> Bool = eq0(7)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard0", functions: [:eq0, :t, :f])

    assert apply(mod, :t, []) == true
    assert apply(mod, :f, []) == false
  end

  test "a single guard with a catch-all fallback runs on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x -> S(Z())\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard1", functions: [:classify, :a, :b])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
  end

  test "a chain of guards falls through to the correct arm on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x when x == 1 -> S(Z())\n" <>
        "    x -> S(S(Z()))\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\n" <>
        "  fn c() -> Nat = classify(9)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard2", functions: [:classify, :a, :b, :c])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
    assert apply(mod, :c, []) == {:S, {:S, :Z}}
  end

  test "a guard whose test is false and has no fallback is rejected (non-exhaustive)" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x when x == 1 -> S(Z())\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
