defmodule Cure.Stdlib.OtpRecursiveTransferTest do
  @moduledoc """
  `Std.Otp.RecursiveTransfer` — the syntax-derived interface transfer for recursive
  behaviours (`infer(BRec)`). Pins that the transfer is monotone for every body (`tset_mono`,
  the hypothesis the finite fixpoint theorem needs) and that `rec_fixed` reads off the
  fixed-point property (`f(infer) sub infer`) at a concrete recursive body via `map_lfp_le`.
  Cross-checked against Idris (oracle `recursive_transfer`); re-checked every build via the
  stdlib preload.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.RecursiveTransfer")
  end

  test "rec_fixed yields the fixed-point property for a concrete recursive body" do
    # mu X. send TA; recv TB; X  — a recursive loop whose inferred interface is {TA, TB}.
    # rec_fixed proves applying the derived transfer to that interface stays within it.
    src = """
    mod RtInst
      use Std.Otp.FiniteFixpoint
      use Std.Otp.RecursiveTransfer
      fn loop_body() -> RBody = RSend(TA, RRecv(TB, RVar()))
      fn ex() -> Sub(tset(loop_body(), rec_infer(loop_body())), rec_infer(loop_body())) =
        rec_fixed(loop_body())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
