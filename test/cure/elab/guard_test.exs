defmodule Cure.Elab.GuardTest do
  @moduledoc """
  Boolean `when` guards on a variable/catch-all pattern desugar to a chain of
  `bool_elim`: `match n | x when g -> a | x -> b` becomes `bool_elim g a b`,
  with each guard test its own Boolean elimination and the final unguarded
  catch-all closing the chain (the fall-through when every guard is false).

  Guards need surface comparison operators to elaborate, so `{:binary_op}`
  lowers to a builtin-op global spine (K2, spec 2026-07-09; e.g. `x == 0` ->
  `int_eq x 0`). Both build on the committed `bool_elim`; no kernel change.
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

  test "multi-parameter function clauses bind tuple leaves in guards and bodies" do
    src = """
    mod M
      fn choose(char: Char, fallback: Char) -> Char
        | char, fallback when char == '.' -> char
        | _, fallback -> fallback

      fn hit() -> Char = choose('.', 'x')
      fn miss() -> Char = choose('a', 'x')
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.GuardMulti", functions: [:choose, :hit, :miss])

    assert apply(mod, :hit, []) == ?.
    assert apply(mod, :miss, []) == ?x
  end

  test "where helpers support one structural parameter column across arities 2 through 6" do
    src = """
    mod M
      use Std.List

      fn arity2(values: List(Int), a: Int) -> Int = classify2(values, a)
      where
        fn classify2(values: List(Int), a: Int) -> Int
          | [], a -> a
          | _, _ -> 20

      fn arity3(a: Int, values: List(Int), b: Int) -> Int = classify3(a, values, b)
      where
        fn classify3(a: Int, values: List(Int), b: Int) -> Int
          | a, [], b -> a + b
          | _, _, _ -> 30

      fn arity4(a: Int, b: Int, c: Int, values: List(Int)) -> Int = classify4(a, b, c, values)
      where
        fn classify4(a: Int, b: Int, c: Int, values: List(Int)) -> Int
          | a, b, c, [] -> a + b + c
          | _, _, _, _ -> 40

      fn arity5(a: Int, values: List(Int), b: Int, c: Int, d: Int) -> Int = classify5(a, values, b, c, d)
      where
        fn classify5(a: Int, values: List(Int), b: Int, c: Int, d: Int) -> Int
          | a, [], b, c, d -> a + b + c + d
          | _, _, _, _, _ -> 50

      fn arity6(values: List(Int), a: Int, b: Int, c: Int, d: Int, e: Int) -> Int = classify6(values, a, b, c, d, e)
      where
        fn classify6(values: List(Int), a: Int, b: Int, c: Int, d: Int, e: Int) -> Int
          | [], a, b, c, d, e -> a + b + c + d + e
          | _, _, _, _, _, _ -> 60

      fn a2_empty() -> Int = arity2([], 7)
      fn a2_present() -> Int = arity2([1], 7)
      fn a3_empty() -> Int = arity3(2, [], 3)
      fn a3_present() -> Int = arity3(2, [1], 3)
      fn a4_empty() -> Int = arity4(1, 2, 3, [])
      fn a4_present() -> Int = arity4(1, 2, 3, [1])
      fn a5_empty() -> Int = arity5(1, [], 2, 3, 4)
      fn a5_present() -> Int = arity5(1, [1], 2, 3, 4)
      fn a6_empty() -> Int = arity6([], 1, 2, 3, 4, 5)
      fn a6_present() -> Int = arity6([1], 1, 2, 3, 4, 5)
    end
    """

    {:ok, env} = Program.elaborate(src)
    roots = [
      :a2_empty, :a2_present, :a3_empty, :a3_present, :a4_empty,
      :a4_present, :a5_empty, :a5_present, :a6_empty, :a6_present
    ]
    functions = Program.reachable_def_names(env, roots)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.WhereStructuralColumn", functions: functions)

    assert apply(mod, :a2_empty, []) == 7
    assert apply(mod, :a2_present, []) == 20
    assert apply(mod, :a3_empty, []) == 5
    assert apply(mod, :a3_present, []) == 30
    assert apply(mod, :a4_empty, []) == 6
    assert apply(mod, :a4_present, []) == 40
    assert apply(mod, :a5_empty, []) == 10
    assert apply(mod, :a5_present, []) == 50
    assert apply(mod, :a6_empty, []) == 15
    assert apply(mod, :a6_present, []) == 60
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
