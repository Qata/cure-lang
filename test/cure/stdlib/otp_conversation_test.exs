defmodule Cure.Stdlib.OtpConversationTest do
  @moduledoc """
  `Std.Otp.Conversation` — whole-conversation protocol ordering. A protocol-directed selective
  receive extracts messages in the protocol's order even when the mailbox arrived out of order;
  `conv_order` proves the received conversation equals the protocol's tag sequence. Cross-checked
  against Idris (oracle `conversation`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Conversation")
  end

  test "a protocol-directed conversation receives in protocol order despite out-of-order arrival" do
    # Protocol expects TA then TB. The mailbox ARRIVED as [TB, TA] (out of order). The
    # conversation receives TA (skipping TB), then TB — the received sequence [TA, TB] equals
    # the protocol order, which conv_order certifies.
    src = """
    mod CvInst
      use Std.Otp.Conversation
      fn sv1() -> SingleRecv(TA, BCons(TB, BCons(TA, BNil())), BCons(TB, BNil())) = SVSkip(SVHere())
      fn sv2() -> SingleRecv(TB, BCons(TB, BNil()), BNil()) = SVHere()
      fn cdone() -> ConvRecv(PDone(), BNil(), BNil(), MNil()) = CRDone()
      fn cr2() -> ConvRecv(PExpect(TB, PDone()), BCons(TB, BNil()), BNil(), MCons(TB, MNil())) =
        CRStep(sv2(), cdone())
      fn cr() -> ConvRecv(PExpect(TA, PExpect(TB, PDone())), BCons(TB, BCons(TA, BNil())), BNil(), MCons(TA, MCons(TB, MNil()))) =
        CRStep(sv1(), cr2())
      fn ordered() -> Equivalent(MList, MCons(TA, MCons(TB, MNil())), ptags(PExpect(TA, PExpect(TB, PDone())))) =
        conv_order(cr())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
