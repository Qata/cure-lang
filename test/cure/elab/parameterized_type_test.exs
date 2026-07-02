defmodule Cure.Elab.ParameterizedTypeTest do
  @moduledoc """
  Parameterized (polymorphic) data types — `type List(a) = Nil | Cons(a, List(a))`,
  `Maybe`, `Box` (Idris parity). Two gaps were closed:

    * `elaborate_index_telescope` did `Keyword.fetch!(pmeta, :type)`, which *crashed*
      on a bare type parameter (`{:param, [], "a"}` — no explicit kind), so even a
      parameterized GADT (`type Vec(a) indices …`) raised `KeyError`. A bare
      parameter ranges over types, so its kind now defaults to `Type`.
    * the `:enum` container elaborator ignored `type_params` entirely. A
      parameterized enum's positional variants are now synthesized into GADT
      constructor signatures (each returning the family applied to its own
      parameters) and elaborated through the shared parameterized-family path with
      an empty index telescope.

  Oracle `poly/pl01_maybe` + `poly/pl02_list` pin accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a single-parameter box constructs, matches, and runs" do
    src =
      @nat <>
        "  type Box(a) = MkBox(a)\n  fn un(b: Box(Nat)) -> Nat = match b\n    MkBox(x) -> x\n" <>
        "  fn g() -> Nat = un(MkBox(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PBox", functions: [:un, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a Maybe-shaped type with a nullary and a unary constructor runs" do
    src =
      @nat <>
        "  type Opt(a) = None | Some(a)\n  fn get(d: Nat, o: Opt(Nat)) -> Nat = match o\n" <>
        "    Some(x) -> x\n    None() -> d\n  fn g() -> Nat = get(Z(), Some(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.POpt", functions: [:get, :g])

    # get(Z, Some(S(Z))) = S(Z).
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a recursive polymorphic list constructs, matches, and runs" do
    src =
      @nat <>
        "  type Lst(a) = Nil | Cons(a, Lst(a))\n  fn hd(d: Nat, l: Lst(Nat)) -> Nat = match l\n" <>
        "    Cons(x, xs) -> x\n    Nil() -> d\n  fn g() -> Nat = hd(Z(), Cons(S(Z()), Nil()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PList", functions: [:hd, :g])

    # hd(Z, Cons(S(Z), Nil)) = S(Z).
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a bare-parameter GADT (Vec) no longer crashes the elaborator" do
    # Regression guard for the Keyword.fetch!(:type) crash on `{:param, [], \"a\"}`.
    src =
      @nat <>
        "  type Vec(a) indices (n: Nat)\n    VNil : Vec(a, Z)\n" <>
        "    VCons : a -> Vec(a, n) -> Vec(a, S(n))\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
