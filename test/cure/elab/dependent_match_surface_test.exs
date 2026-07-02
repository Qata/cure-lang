defmodule Cure.Elab.DependentMatchSurfaceTest do
  @moduledoc """
  Surface acceptance for sub-project ④ (spec §2, §6). Programs go through the
  real pipeline via Cure.Elab.Program.elaborate/1. Negatives assert the exact
  error atom (spec §7).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @vec """
  type Nat = Z | S(Nat)
  type Vector(a: Type) indices (n: Nat)
    empty : Vector(a, Z)
    prepend : a -> Vector(a, n) -> Vector(a, S(n))
  """

  # Pre-impl: {:error, :coverage}. Post: {:ok, _} — prepend is unreachable at Z,
  # so the elaborator discharges it and the kernel's coverage check passes.
  test "(A) a match omitting an impossible constructor elaborates" do
    src = @vec <> """
    fn only_empty({a: Type}, xs: Vector(a, Z)) -> Nat = match xs
      empty() -> Z()
    """
    assert {:ok, _env} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :coverage} (kernel). Post: {:error, {:missing_branch, :prepend}}.
  test "(A) a match omitting a REACHABLE constructor is a missing-branch error" do
    src = @vec <> """
    fn bad({a: Type}, {n: Nat}, xs: Vector(a, n)) -> Nat = match xs
      empty() -> Z()
    """
    assert {:error, {:missing_branch, :prepend}} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :unknown_global} (impossible lexes as an identifier body).
  # Post: {:ok, _} — the branch is genuinely unreachable and accepted.
  test "(A) an explicit `-> impossible` on an unreachable branch elaborates" do
    src = @vec <> """
    fn ei({a: Type}, xs: Vector(a, Z)) -> Nat = match xs
      empty() -> Z()
      prepend(x, rest) -> impossible
    """
    assert {:ok, _env} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :unknown_global}. Post: {:error, {:reachable_impossible, :prepend}}.
  test "(A) a mis-marked `-> impossible` on a reachable branch is rejected" do
    src = @vec <> """
    fn mi({a: Type}, {n: Nat}, xs: Vector(a, n)) -> Nat = match xs
      empty() -> Z()
      prepend(x, rest) -> impossible
    """
    assert {:error, {:reachable_impossible, :prepend}} = Program.elaborate(src)
  end
end
