defmodule Cure.Elab.LargeEliminationTest do
  @moduledoc """
  Large elimination: a value-scrutinee `match` whose branches return DIFFERENT
  types, i.e. a type-level selector `Foci : Kind -> Type`. This is the kernel
  capability that Std.Optic's kind-indexed representation rests on (spec
  2026-07-11-std-optic-design §4: `Foci(k)` selects the per-kind optic rep).

  The oracle twin is `test/oracle/largeelim/le01_foci_selector.{cure,idr}`
  (cure=accept, idris=accept, relation=same). These tests lock in that the
  elaborator not only ACCEPTS the selector but genuinely REDUCES it: the negative
  control fails precisely because `Foci(KAffine)` computes to `Two` and `MkUnit`
  is foreign to `Two`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @selector """
    type Kind = KLens | KAffine | KTraversal
    type Unit = MkUnit
    type Two = T | F
    fn Foci(k: Kind) -> Type = match k
      KLens -> Unit
      KAffine -> Two
      KTraversal -> Unit
  """

  test "selector matching to different types elaborates, and reduces at each kind" do
    src = """
    mod LE
    #{@selector}
      fn mk_lens() -> Foci(KLens) = MkUnit
      fn ok_affine() -> Foci(KAffine) = T
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "negative control: a ctor foreign to the reduced type is rejected" do
    # `Foci(KAffine)` reduces to `Two`; `MkUnit` is a ctor of `Unit`, not `Two`,
    # so this must be rejected. A pass here proves the selector genuinely computes
    # rather than accepting any body at a computed type.
    src = """
    mod LENeg
    #{@selector}
      fn bad() -> Foci(KAffine) = MkUnit
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
