defmodule Cure.Elab.WithAbstractionTest do
  @moduledoc """
  `with`-abstraction, capability A (spec: block-form `with <expr>` that refines
  the GOAL by the scrutinee's VALUE). Programs go through the real pipeline via
  `Cure.Elab.Program.elaborate/1`, which type-checks via the elaborator + kernel
  (no codegen). The differential vs. `match` is that `with` value-abstracts the
  scrutinee EXPRESSION into the motive, so each branch's goal is refined to the
  branch constructor; `match`'s motive only refines type indices.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # SNat is a singleton family indexed by a Nat; `toS` reflects a Nat value into
  # its singleton. `g` is a stuck (identity-by-match) function, so `g(n)` does
  # NOT reduce — the goal `SNat(g(n))` genuinely mentions the scrutinee
  # expression, forcing value-abstraction to do real work.
  @preamble """
  type Nat = Z | S(Nat)
  type SNat indices (n: Nat)
    szero : SNat(Z)
    ssuc : SNat(n) -> SNat(S(n))
  fn g(m: Nat) -> Nat = match m
    Z() -> Z()
    S(k) -> S(k)
  fn toS(m: Nat) -> SNat(m) = match m
    Z() -> szero()
    S(j) -> ssuc(toS(j))
  """

  test "(wi01) `with g(n)` refines the goal SNat(g(n)) per branch" do
    src =
      @preamble <>
        """
        fn foo(n: Nat) -> SNat(g(n)) =
          with g(n)
            Z() -> szero()
            S(k) -> ssuc(toS(k))
        """

    assert {:ok, _env} = Program.elaborate(src)
  end

  # Capability B: `proof <name>` binds the scrutinee equation
  # `Eq(Nat, g(n), pat)` in each branch. `lemma` demands exactly that equation,
  # so the body only type-checks with the bound proof — making it load-bearing.
  @proof_preamble """
  type Nat = Z | S(Nat)
  fn g(m: Nat) -> Nat = match m
    Z() -> Z()
    S(k) -> S(k)
  fn lemma(a: Nat, b: Nat, eq: Eq(Nat, a, b)) -> Nat = b
  """

  test "(wi04) `with g(n) proof pf` binds Eq(g(n), pat), consumed by a lemma" do
    src =
      @proof_preamble <>
        """
        fn foo(n: Nat) -> Nat =
          with g(n) proof pf
            Z() -> lemma(g(n), Z(), pf)
            S(k) -> lemma(g(n), S(k), pf)
        """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "(differential) the SAME body WITHOUT `proof` is REJECTED (pf unbound)" do
    # Plain capability-A `with` does not bind `pf`; the lemma call references an
    # unbound variable, so it must fail — proving the `proof` clause is
    # load-bearing. (Not an oracle probe: Idris would report an unbound name too,
    # but the point is the Cure-side binding, so keep it a unit test.)
    src =
      @proof_preamble <>
        """
        fn foo(n: Nat) -> Nat =
          with g(n)
            Z() -> lemma(g(n), Z(), pf)
            S(k) -> lemma(g(n), S(k), pf)
        """

    assert {:error, _} = Program.elaborate(src)
  end

  test "(differential) plain `match g(n)` for the SAME goal is REJECTED" do
    # `match` cannot refine the goal by the scrutinee's value: `g(n)` is not an
    # index variable, so the motive stays the constant `SNat(g(n))` and each
    # branch body (e.g. `szero() : SNat(Z)`) fails to convert. This is the
    # capability `with` adds; it must NOT be an oracle probe (Idris `case` would
    # refine it and muddy the differential).
    src =
      @preamble <>
        """
        fn foo(n: Nat) -> SNat(g(n)) =
          match g(n)
            Z() -> szero()
            S(k) -> ssuc(toS(k))
        """

    assert {:error, _} = Program.elaborate(src)
  end
end
