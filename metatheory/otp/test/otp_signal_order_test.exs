defmodule Cure.Stdlib.OtpSignalOrderTest do
  @moduledoc """
  `Std.Otp.SignalOrder` — Erlang's KWC per-sender signal ordering. A mailbox is an interleaving
  of the per-sender streams; `proj_left`/`proj_right` prove that projecting the mailbox to one
  sender recovers exactly that sender's stream in order, so each sender's signals stay FIFO
  however the two interleave. Cross-checked against Idris (oracle `signal_order`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.SignalOrder")
  end

  test "projecting an interleaved mailbox to a sender recovers that sender's order" do
    # A sends TA, B sends TB; the mailbox interleaves them as [A:TA, B:TB]. Projecting to SA
    # recovers exactly [A:TA] — sender A's signal order is preserved.
    src = """
    mod SoInst
      use Std.Otp.SignalOrder
      fn il() -> Interleave(MCons(MkMsg(SA, TA), MNil()), MCons(MkMsg(SB, TB), MNil()), MCons(MkMsg(SA, TA), MCons(MkMsg(SB, TB), MNil()))) =
        ILLeft(ILRight(ILNil()))
      fn a_preserved() -> Equivalent(MList, proj(SA, MCons(MkMsg(SA, TA), MCons(MkMsg(SB, TB), MNil()))), MCons(MkMsg(SA, TA), MNil())) =
        proj_left(il())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
