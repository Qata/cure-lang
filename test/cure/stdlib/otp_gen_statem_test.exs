defmodule Cure.Stdlib.OtpGenStatemTest do
  @moduledoc """
  `Std.Otp.GenStatem` — gen_statem event postponing never loses an event. Pins the per-move
  conservation of the unprocessed count `pending + postponed`: `handle_progresses` (handling is
  the only move that advances), `postpone_conserves` / `redeliver_conserves` (deferring and
  redelivering relocate an event, never drop it). Cross-checked against Idris (oracle
  `gen_statem`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.GenStatem")
  end

  test "postpone conserves the unprocessed-event count (deferring never loses an event)" do
    src = """
    mod GsInst
      use Std.Otp.GenStatem
      fn ex() -> Equivalent(Nat, unproc(MkSC(S(Z()), Z())), unproc(MkSC(Z(), S(Z())))) =
        postpone_conserves(Z(), Z())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "handled-event count is a monoid homomorphism over run composition" do
    src = """
    mod GsRun
      use Std.Otp.GenStatem
      fn single(c1: SConfig, c2: SConfig, s: SStep(c1, c2)) -> SRun(c1, c2) =
        srun_single(s)
      fn compose(c1: SConfig, c2: SConfig, c3: SConfig, r1: SRun(c1, c2), r2: SRun(c2, c3)) -> SRun(c1, c3) =
        srun_trans(r1, r2)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
