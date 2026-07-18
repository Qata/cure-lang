defmodule Cure.Stdlib.OtpLifecycleTest do
  @moduledoc """
  `Std.Otp.Lifecycle` — the typed gen_server/gen_statem callback lifecycle. Phases enforce the
  OTP callback order: `init_only` (init is the only first callback), `nothing_reinits` (no
  re-initialization), `terminated_absorbing` + `no_resurrection` (a terminated server stays
  terminated). Cross-checked against Idris (oracle `lifecycle`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Lifecycle")
  end

  test "a well-typed lifecycle runs init, handles requests, stops, then terminates" do
    src = """
    mod LcInst
      use Std.Otp.Lifecycle
      fn full() -> Lifecycle(PInit(), PTerminated()) =
        LStep(CbInit(), LStep(CbCall(), LStep(CbStop(), LStep(CbTerminate(), LEnd()))))
      fn init_forces() -> Equivalent(Phase, PRunning(), PRunning()) =
        init_only(CbInit())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a request callback cannot run before init (from PInit only init is well-typed)" do
    # CbCall is Callback(PRunning, PRunning); using it as the first step from PInit must reject.
    src = """
    mod LcBad
      use Std.Otp.Lifecycle
      fn bad() -> Lifecycle(PInit(), PRunning()) = LStep(CbCall(), LEnd())
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
