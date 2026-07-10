defmodule Cure.Elab.LetBindOnceTest do
  @moduledoc """
  `let x = e ⏎ body` must elaborate to the Core `{:let, ty, e, body}` binder, so
  `e` occurs **once** in the term regardless of how often `x` is used.

  Before the `:let` former existed, `elaborate_let_block/5` eliminated the binding
  by *surface substitution*: `e` was re-elaborated at every use site and dropped
  entirely at zero uses. That is the recorded root cause of the let-duplication
  and join-point bugs, and it is unsound the moment a linear value passes through
  it — the elaborator manufactures the aliasing the type system forbids.

  These tests assert the observable consequences (occurrence count in the
  elaborated Core, and evaluation-order-visible binding structure), not the shape
  of any private function.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @nat "  type Nat = Z | S(Nat)\n"

  # Count subterms structurally equal to `needle` anywhere in `term`.
  defp occurrences(term, needle) when term == needle, do: 1

  defp occurrences(term, needle) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.reduce(0, &(occurrences(&1, needle) + &2))

  defp occurrences(list, needle) when is_list(list),
    do: Enum.reduce(list, 0, &(occurrences(&1, needle) + &2))

  defp occurrences(_, _), do: 0

  defp lets(term) when is_tuple(term) do
    self = if elem(term, 0) == :let, do: 1, else: 0
    self + (term |> Tuple.to_list() |> Enum.reduce(0, &(lets(&1) + &2)))
  end

  defp lets(list) when is_list(list), do: Enum.reduce(list, 0, &(lets(&1) + &2))
  defp lets(_), do: 0

  defp body_of!(src, fname) do
    assert {:ok, env} = Program.elaborate(src)
    %{body: body} = Map.fetch!(env.defs, fname)
    body
  end

  describe "bind-once" do
    test "a let used twice binds its rhs exactly once" do
      src =
        "mod L\n" <>
          @nat <>
          "  fn add(a: Nat, b: Nat) -> Nat = a\n" <>
          "  fn f(n: Nat) -> Nat =\n    let m = S(n)\n    add(m, m)\n"

      body = body_of!(src, :f)

      # `S(n)` is the rhs. Under surface substitution it appears twice.
      assert occurrences(body, {:ctor, :S, [{:var, 0}]}) == 1
      assert lets(body) == 1
    end

    test "a let used zero times still binds its rhs (it is not dropped)" do
      src = "mod L\n" <> @nat <> "  fn f(n: Nat) -> Nat =\n    let m = S(n)\n    n\n"
      body = body_of!(src, :f)

      assert lets(body) == 1
      assert occurrences(body, {:ctor, :S, [{:var, 0}]}) == 1
    end

    test "chained lets nest rather than duplicate" do
      src =
        "mod L\n" <>
          @nat <>
          "  fn add(a: Nat, b: Nat) -> Nat = a\n" <>
          "  fn f(n: Nat) -> Nat =\n    let a = S(n)\n    let b = S(a)\n    add(b, b)\n"

      body = body_of!(src, :f)
      assert lets(body) == 2
    end
  end

  describe "ζ keeps dependent lets working" do
    # This is the property surface substitution used to buy and a β-redex loses.
    # It must survive the switch to the `:let` binder.
    test "a let-bound value is usable at a dependent (indexed) type" do
      src =
        "mod L\n" <>
          @nat <>
          "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
          "  fn g(n: Nat, s: SNat(n)) -> SNat(S(n)) =\n    let t = ssuc(s)\n    t\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "a let-bound Nat is transparent in a later index position" do
      src =
        "mod L\n" <>
          @nat <>
          "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
          "  fn h() -> SNat(S(Z())) =\n    let k = Z()\n    ssuc(szero())\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "soundness control: a body ill-typed under the binding is still rejected" do
      src =
        "mod L\n" <>
          @nat <>
          "  type SNat indices (k: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(k) -> SNat(S(k))\n" <>
          "  fn bad(n: Nat) -> SNat(n) =\n    let m = S(n)\n    m\n"

      assert {:error, _} = Program.elaborate(src)
    end
  end
end
