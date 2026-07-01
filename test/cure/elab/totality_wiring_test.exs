defmodule Cure.Elab.TotalityWiringTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @types """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  """

  @gadt """
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  test "a total type-level function is certified; the whole program elaborates" do
    src = @types <> "fn andd(x: Dec, y: Dec) -> Dec = x\n" <> @gadt
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a non-total function used in a type is rejected (totality required)" do
    # andd is self-recursive (non-total) yet appears in SF's computed index,
    # so it is type-level and MUST be total — §6 negative #3.
    src = @types <> "fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)\n" <> @gadt
    assert {:error, {:totality_required, :andd}} = Program.elaborate(src)
  end

  test "a non-total function used only at runtime is NOT required to be total" do
    # loop is self-recursive but referenced in no type ⇒ stays partial, allowed.
    src =
      @types <>
        "fn andd(x: Dec, y: Dec) -> Dec = x\n" <>
        @gadt <>
        "fn loop(x: Dec) -> Dec = loop(x)\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
