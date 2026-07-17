defmodule Cure.Stdlib.OtpSessionMailboxTest do
  @moduledoc """
  `Std.Otp.SessionMailbox` — the de'Liguoro–Padovani encoding of binary session endpoints into
  mailbox (multiset) types. `recvs_dual` proves the encoding is sound: an endpoint's mailbox
  contents equal exactly what its dual peer sends. Cross-checked against Idris (oracle
  `session_mailbox`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.SessionMailbox")
  end

  test "recvs_dual: an endpoint's mailbox equals what its dual peer sends" do
    # Endpoint sends TA then receives TB. Its dual receives TA then sends TB, so the dual's
    # mailbox (recvs) is {TB} — exactly what the original endpoint sends. recvs_dual certifies it.
    src = """
    mod SmInst
      use Std.Otp.SessionMailbox
      fn ep() -> Local = LSend(TA, LRecv(TB, LEnd()))
      fn fidelity() -> Equivalent(MS, recvs(dual(LSend(TA, LRecv(TB, LEnd())))), sends(LSend(TA, LRecv(TB, LEnd())))) =
        recvs_dual(LSend(TA, LRecv(TB, LEnd())))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "sends_dual: what an endpoint sends equals what its dual peer receives" do
    src = """
    mod SmMirror
      use Std.Otp.SessionMailbox
      fn mirror() -> Equivalent(MS, sends(dual(LRecv(TA, LEnd()))), recvs(LRecv(TA, LEnd()))) =
        sends_dual(LRecv(TA, LEnd()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
