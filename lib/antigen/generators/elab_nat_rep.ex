defmodule Antigen.Generators.ElabNatRep do
  @moduledoc """
  Representation-agreement corpus for Nat->Int erasure (spec
  2026-07-08-nat-int-erasure §3): closed, self-contained programs over the
  CANONICAL auto-prelude Std.Nat (no local `type Nat`, no `use`) with local
  arithmetic defs and a 0-ary `main`. The assay compares the kernel's
  certified-δ normalisation of `main` (decoded ctor spine) against BEAM
  execution of the emitted module. Fixed cells cover each lowering rule;
  seeded cells add depth-varied arithmetic expressions (deterministic per
  seed — no runtime randomness).
  """

  alias Antigen.Challenge

  @defs """
    fn add(a: Nat, b: Nat) -> Nat = match a
      Z() -> b
      S(k) -> S(add(k, b))
    fn dbl(n: Nat) -> Nat = match n
      Z() -> Z()
      S(k) -> S(S(dbl(k)))
    fn pred(n: Nat) -> Nat = match n
      Z() -> Z()
      S(k) -> k
  """

  @functions [:add, :dbl, :pred, :main]

  defp program(main_expr),
    do: "mod P\n" <> @defs <> "  fn main() -> Nat = " <> main_expr <> "\nend\n"

  defp nat_lit(0), do: "Z()"
  defp nat_lit(n) when n > 0, do: "S(" <> nat_lit(n - 1) <> ")"

  @fixed [
    {"ctor/zero", "Z()"},
    {"ctor/three", "S(S(S(Z())))"},
    {"match/pred", "pred(S(S(Z())))"},
    {"match/pred_zero", "pred(Z())"},
    {"arith/add", "add(S(S(Z())), S(S(S(Z()))))"},
    {"arith/dbl", "dbl(S(S(Z())))"},
    {"arith/nested", "add(dbl(S(Z())), pred(S(S(S(Z())))))"},
    {"arith/deep", "dbl(dbl(dbl(S(Z()))))"}
  ]

  # Deterministic seeded arithmetic expressions (pure function of the seed —
  # Antigen scripts/tests must not use runtime randomness).
  defp seeded_expr(seed) do
    a = rem(seed * 7, 5)
    b = rem(seed * 13, 4)

    case rem(seed, 3) do
      0 -> "add(" <> nat_lit(a) <> ", dbl(" <> nat_lit(b) <> "))"
      1 -> "dbl(add(" <> nat_lit(a) <> ", " <> nat_lit(b) <> "))"
      2 -> "pred(add(" <> nat_lit(a + 1) <> ", " <> nat_lit(b) <> "))"
    end
  end

  @doc "All representation-agreement challenges (8 fixed + 6 seeded)."
  @spec nat_rep_challenges() :: [Challenge.t()]
  def nat_rep_challenges do
    fixed =
      Enum.map(@fixed, fn {id, expr} ->
        challenge(id, expr)
      end)

    seeded = for s <- 1..6, do: challenge("seeded/#{s}", seeded_expr(s))

    fixed ++ seeded
  end

  @doc "Catalog ids with their main expressions."
  @spec catalog() :: [{String.t(), String.t()}]
  def catalog, do: Enum.map(@fixed, fn {id, expr} -> {id, expr} end)

  @doc "Full module source for a fixed cell id."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case Enum.find(@fixed, fn {i, _} -> i == id end) do
      {_id, expr} -> program(expr)
      nil -> nil
    end
  end

  defp challenge(id, expr) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/nat_rep",
      label: :agree,
      payload: %{id: id, src: program(expr), functions: @functions},
      note: "kernel-vs-BEAM agreement for `#{expr}`"
    )
  end
end
