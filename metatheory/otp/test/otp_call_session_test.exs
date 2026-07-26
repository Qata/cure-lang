defmodule Cure.Stdlib.OtpCallSessionTest do
  @moduledoc """
  `Std.Otp.CallSession` — gen_server:call as a dependent binary session whose reply tag is
  computed from the request (`reply_for`). `call_duality` proves the client/server endpoints are
  dual for every request; `call_compat` proves the dependent request/reply exchange is compatible.
  Cross-checked against Idris (oracle `call_session`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.CallSession")
  end

  test "call_compat: a concrete RGet call is a compatible request/reply exchange" do
    # A call with request RGet expects reply VNat; call_compat certifies the exchange is
    # communication-safe (send request, receive VNat reply, end).
    src = """
    mod CsInst
      use Std.Otp.CallSession
      fn safe() -> Compat(client(RGet()), server(RGet())) = call_compat(RGet())
      fn dual_ok() -> Equivalent(SType, client(RPut()), dual(server(RPut()))) = call_duality(RPut())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "the reply tag is the computed reply_for of the request" do
    # RGet's reply is VNat, RPut's is VUnit — the client's continuation carries exactly reply_for.
    src = """
    mod CsReply
      use Std.Otp.CallSession
      fn get_reply() -> Equivalent(SType, client(RGet()), SSendReq(RGet(), SRecvRep(VNat(), SEnd()))) =
        reflexive(SSendReq(RGet(), SRecvRep(VNat(), SEnd())))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
