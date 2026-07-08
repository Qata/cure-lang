defmodule Cure.Elab.NamedImplicitTailTest do
  @moduledoc """
  Ledger row #5 tail (spec 2026-07-08-dotsyntax-tail-design): the three
  named-implicit caveats C-a / C-b / C-c. Each test names the caveat it pins.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Vec with an erased implicit index arg `n` on vcons. `{n = .k}` is a
  # named-implicit annotation on that erased slot.
  @preamble """
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
  """

  defp mod(body), do: "mod P\n" <> @preamble <> body <> "end\n"

  describe "C-b: named-implicit patterns never reach expression position" do
    test "branch body referencing the scrutinee elaborates (refine_scrutinee_in_body site)" do
      src =
        mod("""
          fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
            vcons({n = .k}, h, t) -> v
        """)

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "as-pattern over a named-implicit ctor pattern with body ref elaborates (strip_as_patterns site)" do
      src =
        mod("""
          fn g({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
            w @ vcons({n = .k}, h, t) -> w
        """)

      assert {:ok, _env} = Program.elaborate(src)
    end
  end

  # Carried + forced mixed shape: `H`'s FIRST index is ctor-pinned (forced:
  # matching `hmk` against `H(S(j), …)` pins `m := j`), while the SECOND is a
  # stuck function index carried via the sibling `w` (detect_carried_index).
  @carried_preamble """
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type H indices (n: Nat, xs: SList)
      hmk : H(S(m), app(as, bs))
    type G indices (xs: SList)
      gwrap : G(cs)
  """

  defp cmod(body),
    do: "mod P\n  type Nat = Z | S(Nat)\n" <> @carried_preamble <> body <> "end\n"

  describe "C-a: forced check runs on the carried-eq path" do
    test "wrong dot on a carried-eq branch rejects" do
      src =
        cmod("""
          fn f({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
            hmk({m = .(S(j))}) -> Z()
        """)

      assert {:error, {:forced_pattern_mismatch, _, _}} = Program.elaborate(src)
    end

    test "right dot on a carried-eq branch accepts (over-rejection guard)" do
      src =
        cmod("""
          fn g({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
            hmk({m = .j}) -> Z()
        """)

      assert {:ok, _env} = Program.elaborate(src)
    end
  end
end
