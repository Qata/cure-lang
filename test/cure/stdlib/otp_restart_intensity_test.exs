defmodule Cure.Stdlib.OtpRestartIntensityTest do
  @moduledoc """
  `Std.Otp.RestartIntensity` — the `max_restarts` bound: a supervisor carries a restart budget
  (a `Nat` index), `FRestart` consumes one and requires `S(n)` budget, and a zero-budget
  failure has only `FShutdown`. Re-checked every build via the stdlib preload; these tests pin
  the intensity bound — a supervisor cannot restart beyond its budget.

  The bounded-run liveness theorem (`eventually_down`) is E6-blocked in Cure and lives as a
  probe (`docs/research/process-types/probes/restart_intensity_liveness.cure`); it is not
  exercised here.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Phase = Up | Down
    type Sup indices (budget: Nat, phase: Phase)
      Alive   : Sup(n, Up)
      Stopped : Sup(Z, Down)
    type Fail indices (b1: Nat, p1: Phase, b2: Nat, p2: Phase)
      FRestart  : Fail(S(n), Up, n, Up)
      FShutdown : Fail(Z, Up, Z, Down)
    fn on_fail({b1: Nat}, {p1: Phase}, {b2: Nat}, {p2: Phase}, sup: Sup(b1, p1), f: Fail(b1, p1, b2, p2)) -> Sup(b2, p2) = match f
      FRestart()  -> Alive()
      FShutdown() -> Stopped()
  """

  defp verdict(defs) do
    case Program.elaborate("mod RiT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a positive budget restarts (S(Z) -> Z, still Up)" do
    defs = """
      fn restart_step() -> Fail(S(Z), Up, Z, Up) = FRestart()
    """

    assert verdict(defs) == :accept
  end

  test "an exhausted budget shuts down (Z -> Z, Down)" do
    defs = """
      fn shutdown_step() -> Fail(Z, Up, Z, Down) = FShutdown()
    """

    assert verdict(defs) == :accept
  end

  test "a supervisor cannot restart at zero budget (FRestart requires S(n))" do
    # FRestart : Fail(S(n), Up, n, Up); a step from budget Z that keeps running is not a restart.
    defs = """
      fn over_intensity() -> Fail(Z, Up, Z, Up) = FRestart()
    """

    assert verdict(defs) == :reject
  end
end
