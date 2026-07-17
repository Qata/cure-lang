defmodule Cure.Stdlib.OtpMultipartySessionTest do
  @moduledoc """
  `Std.Otp.MultipartySession` — global protocol types projected to per-role local types.
  `projection_duality` proves the coherence result: a two-party global protocol projects to DUAL
  endpoints, so global well-formedness yields local communication safety. Cross-checked against
  Idris (oracle `multiparty_session`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.MultipartySession")
  end

  test "a two-party global projects to dual endpoints (coherence)" do
    # Global: RA sends TA to RB, then RB sends TB to RA, then end. Its projections onto RA and RB
    # are dual, which projection_duality certifies.
    src = """
    mod MpInst
      use Std.Otp.MultipartySession
      fn wf() -> TwoParty(GMsg(RA, RB, TA, GMsg(RB, RA, TB, GEnd()))) =
        TPAB(TA, TPBA(TB, TPEnd()))
      fn coherent() -> Equivalent(Local, project(GMsg(RA, RB, TA, GMsg(RB, RA, TB, GEnd())), RA), dual(project(GMsg(RA, RB, TA, GMsg(RB, RA, TB, GEnd())), RB))) =
        projection_duality(wf())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "firing the head interaction preserves two-party well-formedness (subject reduction)" do
    # GStep fires the head message of the protocol; twoparty_preserved certifies the resulting
    # continuation is still a well-formed two-party protocol.
    src = """
    mod MpStep
      use Std.Otp.MultipartySession
      fn wf() -> TwoParty(GMsg(RA, RB, TA, GMsg(RB, RA, TB, GEnd()))) =
        TPAB(TA, TPBA(TB, TPEnd()))
      fn advanced() -> TwoParty(GMsg(RB, RA, TB, GEnd())) =
        twoparty_preserved(wf(), GFire())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "global_progress: a well-formed non-empty protocol is ready to fire (no deadlock)" do
    src = """
    mod MpProg
      use Std.Otp.MultipartySession
      fn wf() -> TwoParty(GMsg(RA, RB, TA, GEnd())) = TPAB(TA, TPEnd())
      fn ready() -> GProgress(GMsg(RA, RB, TA, GEnd())) = global_progress(wf())
      fn done() -> GProgress(GEnd()) = global_progress(TPEnd())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
