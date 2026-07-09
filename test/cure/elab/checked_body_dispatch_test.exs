defmodule Cure.Elab.CheckedBodyDispatchTest do
  @moduledoc """
  Wave 4: `:list` and `:pickup` function-body / match-arm-body nodes reach CHECKED
  elaboration (receive the declared return type), so a bare `[]` body / `[] -> []`
  arm / `:pickup`-with-`[]`-then-branch pins its element type from the goal instead
  of failing with `{:unsolved_metavariables, :Nil}`. Elaborator-only; closes the
  third-dispatch-layer gap ledgered since Wave 1.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a bare [] top-level body elaborates + runs" do
    src = "mod M\n  fn e() -> List(Int) = []\nend\n"
    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD1", functions: [:e])
    assert apply(mod, :e, []) == []
  end

  test "a [] -> [] arm body elaborates + runs" do
    src =
      "mod M\n  fn f(xs: List(Int)) -> List(Int) =\n" <>
        "    match xs\n      [] -> []\n      [h | t] -> t\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD2", functions: [:f])
    assert apply(mod, :f, [[]]) == []
    assert apply(mod, :f, [[1, 2, 3]]) == [2, 3]
  end

  test "a :pickup body with a bare-[] then-branch elaborates + runs (take shape)" do
    src =
      "mod M\n  fn g(n: Int) -> List(Int) =\n" <>
        "    pickup\n      n <= 0 -> []\n      else -> [n]\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD3", functions: [:g])
    assert apply(mod, :g, [0]) == []
    assert apply(mod, :g, [5]) == [5]
  end

  test "REGRESSION GUARD — head-bearing list body + inferrable pickup still work" do
    src =
      "mod M\n  fn h(x: Int, t: List(Int)) -> List(Int) = [x | t]\n" <>
        "  fn p(xs: List(Int)) -> List(Int) =\n" <>
        "    pickup\n      true -> xs\n      else -> xs\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD4", functions: [:h, :p])
    assert apply(mod, :h, [1, [2, 3]]) == [1, 2, 3]
    assert apply(mod, :p, [[9]]) == [9]
  end

  test "Std.List smoke — a real previously-blocked function (tail) elaborates + runs" do
    # Verbatim tail/2 shape from lib/std/list.cure (its `[] -> []` arm was the
    # blocker). tail is at list.cure:72; copied here with Nat elements.
    src =
      @nat <>
        "  fn tail(xs: List(Nat)) -> List(Nat) =\n" <>
        "    match xs\n      [] -> []\n      [h | t] -> t\nend\n"

    assert {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CBD5", functions: [:tail])
    assert apply(mod, :tail, [[]]) == []
    assert apply(mod, :tail, [[:Z, :Z]]) == [:Z]
  end
end
