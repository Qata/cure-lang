defmodule Cure.Elab.HigherOrderUnifyTest do
  @moduledoc """
  Higher-order unification depth fix (Idris parity): unifying a function-typed
  argument's type `(a) -> b` against a callee's expected `(?a) -> ?b` crosses the
  Π binder, so a metavariable solved inside the codomain was captured one de Bruijn
  level too deep and reappeared mis-levelled in the result type (`{:var, 4}` vs
  `{:var, 5}`). `Cure.Elab.Unify` now tracks binder depth and strengthens a
  metavariable's solution back to the ambient frame before recording it (at depth 0
  — every prior unification — this is the identity). This unblocks re-passing a
  polymorphic function argument, so `map` type-checks and runs.

  Oracle `poly/pl06_polymorphic_map` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @lst "mod M\n  type Nat = Z | S(Nat)\n  type Lst(a) = Nil | Cons(a, Lst(a))\n"

  test "polymorphic map type-checks and runs" do
    src =
      @lst <>
        "  fn map({a}, {b}, f: (a)->b, l: Lst(a)) -> Lst(b) = match l\n" <>
        "    Nil() -> Nil()\n    Cons(x, xs) -> Cons(f(x), map(f, xs))\n" <>
        "  fn s(n: Nat) -> Nat = S(n)\n" <>
        "  fn mklist() -> Lst(Nat) = Cons(Z(), Cons(S(Z()), Nil()))\n" <>
        "  fn g() -> Lst(Nat) = map(s, mklist())\nend\n"

    {:ok, env} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.HoMap", functions: [:map, :s, :mklist, :g])

    # map (+1) [0, 1] = [1, 2]
    assert apply(mod, :g, []) == {:Cons, {:S, :Z}, {:Cons, {:S, {:S, :Z}}, :Nil}}
  end

  test "re-passing a function-typed argument to an implicit-solving call type-checks" do
    # The minimal trigger: `q(f, l)` re-passes `f : (a) -> b` while solving q's own
    # implicit parameters — the case that previously failed :cannot_unify.
    src =
      @lst <>
        "  fn q({a}, {b}, f: (a)->b, l: Lst(a)) -> Lst(b) = match l\n" <>
        "    Nil() -> Nil()\n    Cons(x, xs) -> q(f, xs)\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
