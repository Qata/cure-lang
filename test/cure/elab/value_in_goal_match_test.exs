defmodule Cure.Elab.ValueInGoalMatchTest do
  @moduledoc """
  A dependent `match` whose GOAL mentions the scrutinee VALUE (not just its
  index) — e.g. `Equivalent(NV(n), v, v)`. In each branch the dependent match refines the
  scrutinee to that branch's constructor, so the goal refines to `Equivalent(NV(Z), vz,
  vz)` / `Equivalent(NV(S m), vs s, vs s)`, which `reflexive(ctor)` inhabits. Idris accepts all
  of these (`idris2 --check`, zero errors).

  RED before the fix: the plain-`match` branch computed its checking-mode
  `branch_expected` via an ad-hoc `branch_index_subst` that only inverts when the
  CONSTRUCTOR result index is a variable. For `v : NV(n)` matched by `vz : NV(Z)`
  the pair is `{Z, n}` (Z is not a var), so the scrutinee's index var `n` was
  never inverted to `Z`; the goal stayed `Equivalent(NV(n), vz, vz)` and the body
  `reflexive(vz()) : Equivalent(NV(Z), …)` failed conversion `NV(Z) ≢ NV(n)`. The kernel's own
  `branch_unify` verdict already carries `n := Z` (the `j >= arity` inverse
  clause), and the with-rematch path already uses it; this fix routes the plain
  path through the same verdict.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
    type NV indices (n: Nat)
      vz : NV(Z)
      vs : SNat(n) -> NV(S(n))
    fn toS(m: Nat) -> SNat(m) = match m
      Z() -> szero()
      S(j) -> ssuc(toS(j))
    fn view(n: Nat) -> NV(n) = match n
      Z() -> vz()
      S(m) -> vs(toS(m))
  """
  defp mod(b), do: "mod P\n" <> @preamble <> b <> "end\n"

  test "goal Equivalent(NV(n), v, v), var scrutinee, reflexive(ctor) bodies" do
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
          match v
            vz() -> reflexive(vz())
            vs(s) -> reflexive(vs(s))
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "goal Equivalent(NV(n), v, v), reflexive(v) bodies (value-occurrence in both positions)" do
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
          match v
            vz() -> reflexive(v)
            vs(s) -> reflexive(v)
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "goal Equivalent(NV(n), view(n), view(n)), computed scrutinee" do
    src =
      mod("""
        fn f(n: Nat) -> Equivalent(NV(n), view(n), view(n)) =
          match view(n)
            vz() -> reflexive(vz())
            vs(s) -> reflexive(vs(s))
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "soundness control: an ill-typed body at the refined goal is rejected" do
    # In the vz branch the goal refines to `Equivalent(NV(Z), vz, vz)`. Returning
    # `reflexive(vs(...))` (: Equivalent(NV(S _), vs _, vs _)) must be rejected — the value
    # refinement must not over-accept a mismatched constructor.
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
          match v
            vz() -> reflexive(vs(szero()))
            vs(s) -> reflexive(vs(s))
      """)

    assert {:error, _} = Program.elaborate(src)
  end

  test "control: index-only goal still elaborates (no regression on the plain path)" do
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> NV(n) =
          match v
            vz() -> vz()
            vs(s) -> vs(s)
      """)

    assert {:ok, _} = Program.elaborate(src)
  end
end
