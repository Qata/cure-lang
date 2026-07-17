defmodule Cure.Stdlib.OtpRecursiveAdequacyTest do
  @moduledoc """
  `Std.Otp.RecursiveAdequacy` — BRec coverage: every tag a recursive behaviour sends is a
  member of its inferred fixed-point interface. Pins the coverage induction (`tset_covers`)
  and the capstone `brec_covers`, which carries a send site through the fixed-point witness
  `rec_fixed`. Cross-checked against Idris (oracle `recursive_coverage`); re-checked every
  build via the stdlib preload.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.RecursiveAdequacy")
  end

  test "brec_covers: a recursive body's send tag is in its inferred fixed-point interface" do
    # mu X. send TA; recv TB; X  — TA is sent, so TA's bit is set in the inferred interface.
    src = """
    mod RaInst
      use Std.Otp.FiniteFixpoint
      use Std.Otp.RecursiveTransfer
      use Std.Otp.RecursiveAdequacy
      fn loop_body() -> RBody = RSend(TA, RRecv(TB, RVar()))
      fn covered() -> Equivalent(B, getb(rec_infer(loop_body()), TA), T) =
        brec_covers(loop_body(), TA, RSHere())
      fn handled() -> Handles(TA, denote(rec_infer(loop_body()))) =
        brec_handles(loop_body(), TA, RSHere())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
