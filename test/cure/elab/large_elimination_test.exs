defmodule Cure.Elab.LargeEliminationTest do
  @moduledoc """
  Large elimination: a value-scrutinee `match` whose branches return DIFFERENT
  types, i.e. a type-level selector `FocusShape : OpticKind -> Type`. This is the
  kernel capability that Std.Optic's kind-indexed representation rests on (spec
  2026-07-11-std-optic-design §4: `FocusShape(k)` selects the per-kind optic rep).

  The oracle twin is
  `test/oracle/largeelim/le01_focus_shape_selector.{cure,idr}`
  (cure=accept, idris=accept, relation=same). These tests lock in that the
  elaborator not only ACCEPTS the selector but genuinely REDUCES it: the negative
  control fails precisely because `FocusShape(AffineKind)` computes to `Two` and
  `MkUnit` is foreign to `Two`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @selector """
    type OpticKind = LensKind | AffineKind | TraversalKind
    type Unit = MkUnit
    type Two = T | F
    fn FocusShape(k: OpticKind) -> Type = match k
      LensKind -> Unit
      AffineKind -> Two
      TraversalKind -> Unit
  """

  test "selector matching to different types elaborates, and reduces at each kind" do
    src = """
    mod LE
    #{@selector}
      fn mk_lens() -> FocusShape(LensKind) = MkUnit
      fn ok_affine() -> FocusShape(AffineKind) = T
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "negative control: a ctor foreign to the reduced type is rejected" do
    # `FocusShape(AffineKind)` reduces to `Two`; `MkUnit` is a ctor of `Unit`, not
    # `Two`, so this must be rejected. A pass here proves the selector genuinely
    # computes rather than accepting any body at a computed type.
    src = """
    mod LENeg
    #{@selector}
      fn bad() -> FocusShape(AffineKind) = MkUnit
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
