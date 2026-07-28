defmodule Cure.Stdlib.OtpRecursiveRunTest do
  @moduledoc """
  `Std.Otp.RecursiveRun` — BRec adequacy (operational half): every config reachable by running
  a recursive behaviour is well-typed at its inferred fixed-point interface. Pins the generic
  operational core (`preservation_at`/`adequacy_at`) and the recursive tie-ins: `rec_send_step`
  (a recursive send is a valid step, justified by `brec_handles`) and `rec_adequacy`. The
  end-to-end test runs `mu X. send TA; recv TB; X` one step and proves the resulting config is
  well-typed. Cross-checked against Idris (oracle `recursive_run`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.RecursiveRun")
  end

  test "a config reached by running a recursive behaviour is well-typed at its inferred interface" do
    src = """
    mod RrInst
      use Std.Otp.FiniteFixpoint
      use Std.Otp.InterfaceBridge
      use Std.Otp.RecursiveTransfer
      use Std.Otp.RecursiveAdequacy
      use Std.Otp.RecursiveRun
      fn loop_body() -> RBody = RSend(TA, RRecv(TB, RVar()))
      # Run one step: start, then emit the (inference-justified) send of TA.
      fn one_step_run() -> RunsAt(denote(rec_infer(loop_body())), MkConfig(TCons(TA, TNil), TNil)) =
        RAStep(ra_start(denote(rec_infer(loop_body()))), rec_send_step(loop_body(), TA, RSHere()))
      fn after_send_wt() -> WTat(MkConfig(TCons(TA, TNil), TNil), denote(rec_infer(loop_body()))) =
        rec_adequacy(loop_body(), one_step_run())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
