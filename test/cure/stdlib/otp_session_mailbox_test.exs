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

  test "fork/join: fidelity holds for a parallel composition (mailbox = multiset sum)" do
    # An endpoint forks two sub-sessions (recv TA in parallel with recv TB). Its dual sends TA
    # in parallel with sends TB; recvs_dual certifies the parallel mailbox equals the dual's
    # parallel sends, componentwise.
    src = """
    mod SmPar
      use Std.Otp.SessionMailbox
      fn ep() -> Local = LPar(LRecv(TA, LEnd()), LRecv(TB, LEnd()))
      fn fidelity() -> Equivalent(MS, recvs(dual(LPar(LRecv(TA, LEnd()), LRecv(TB, LEnd())))), sends(LPar(LRecv(TA, LEnd()), LRecv(TB, LEnd())))) =
        recvs_dual(LPar(LRecv(TA, LEnd()), LRecv(TB, LEnd())))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "compat_recv_send: compatible endpoints have balanced mailboxes" do
    # LSend(TA, LEnd) is compatible with LRecv(TA, LEnd); the sender's mailbox (empty) equals the
    # receiver's sends (empty), and the sender's sends {TA} equals the receiver's mailbox {TA}.
    src = """
    mod SmBal
      use Std.Otp.SessionMailbox
      fn c0() -> Compat(LSend(TA, LEnd()), LRecv(TA, LEnd())) = CSR(TA, CEnd())
      fn balanced() -> Equivalent(MS, recvs(LSend(TA, LEnd())), sends(LRecv(TA, LEnd()))) =
        compat_recv_send(CSR(TA, CEnd()))
      fn mirror() -> Equivalent(MS, sends(LSend(TA, LEnd())), recvs(LRecv(TA, LEnd()))) =
        compat_send_recv(CSR(TA, CEnd()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
