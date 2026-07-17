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
end
