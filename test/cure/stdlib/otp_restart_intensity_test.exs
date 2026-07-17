defmodule Cure.Stdlib.OtpRestartIntensityTest do
  @moduledoc """
  `Std.Otp.RestartIntensity` — the `max_restarts` bound: a supervisor carries a restart budget
  (a `Nat` index), `FRestart` consumes one and requires `S(n)` budget, and a zero-budget
  failure has only `FShutdown`. Re-checked every build via the stdlib preload; these tests pin
  the intensity bound — a supervisor cannot restart beyond its budget.

  The bounded-run liveness theorem (`eventually_down`: from budget `n`, `n` restarts then one
  shutdown reach `Down`) is proved in the shipped module and exercised here — it was formerly
  E6-blocked and is now unblocked by the constructor-argument deferral fix.
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
    type FailRun indices (b1: Nat, p1: Phase, b2: Nat, p2: Phase)
      FRDone : FailRun(b, p, b, p)
      FRMore : Fail(b1, p1, bm, pm) -> FailRun(bm, pm, b2, p2) -> FailRun(b1, p1, b2, p2)
    fn eventually_down(n: Nat) -> FailRun(n, Up, Z, Down) = match n
      Z()  -> FRMore(FShutdown(), FRDone())
      S(k) -> FRMore(FRestart(), eventually_down(k))
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

  test "the bounded-run liveness theorem holds at a concrete budget" do
    # A budget-2 supervisor reaches Down after exactly two restarts and one shutdown.
    defs = """
      fn tolerates_two() -> FailRun(S(S(Z)), Up, Z, Down) = eventually_down(S(S(Z)))
    """

    assert verdict(defs) == :accept
  end

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.RestartIntensity")
  end

  test "restart intensity is exact: the canonical run tolerates exactly budget+1 failures" do
    src = """
    mod RiExact
      use Std.Otp.RestartIntensity
      fn exact(n: Nat) -> Equivalent(Nat, run_len(eventually_down(n)), S(n)) =
        eventually_down_len(n)
      fn tolerates_two() -> Equivalent(Nat, run_len(eventually_down(S(S(Z())))), S(S(S(Z())))) =
        eventually_down_len(S(S(Z())))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
