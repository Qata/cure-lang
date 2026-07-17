defmodule Cure.Stdlib.OtpRecursiveSessionTest do
  @moduledoc """
  `Std.Otp.RecursiveSession` — recursive session types (`μX.S`, looping protocols). Pins the
  headline theorem `dual_unfold_commute` (duality commutes with unfolding, so a recursive
  protocol's endpoints stay dual across every iteration) and `rdual_involution`. Cross-checked
  against Idris (oracle `recursive_session`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.RecursiveSession")
  end

  test "duality commutes with unfolding for a recursive server loop" do
    # A server loop mu X. recv TA; send TB; X. dual_unfold_commute certifies that dualizing then
    # unfolding equals unfolding then dualizing. (Annotations match the theorem type exactly to
    # avoid the E11 nested-application conversion gap.)
    src = """
    mod RsInst
      use Std.Otp.RecursiveSession
      fn body() -> RSType = RRecv(TA, RSend(TB, RVar()))
      fn commute() -> Equivalent(RSType, rdual(unfold(RMu(RRecv(TA, RSend(TB, RVar()))))), unfold(RMu(rdual(RRecv(TA, RSend(TB, RVar())))))) =
        dual_unfold_commute(RRecv(TA, RSend(TB, RVar())))
      fn invol() -> Equivalent(RSType, rdual(rdual(RMu(RSend(TA, RVar())))), RMu(RSend(TA, RVar()))) =
        rdual_involution(RMu(RSend(TA, RVar())))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "duality commutes with unfolding in general form (non-recursive head)" do
    # rdual_unfold applies at any shape; on a send head unfold is the identity and dual commutes
    # structurally.
    src = """
    mod RsGen
      use Std.Otp.RecursiveSession
      fn gen() -> Equivalent(RSType, rdual(unfold(RSend(TA, RVar()))), unfold(rdual(RSend(TA, RVar())))) =
        rdual_unfold(RSend(TA, RVar()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
