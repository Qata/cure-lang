defmodule Cure.Stdlib.OtpExitSignalTest do
  @moduledoc """
  `Std.Otp.ExitSignal` — reason-dependent exit-signal propagation: `Step` is indexed by the
  exit `Reason` (`Normal`/`Abnormal`/`Kill`), so the dispatch is type-level. The proof is
  re-checked every build via the stdlib preload; these tests pin the guarantees OTP
  programmers rely on — a `normal` exit never kills a non-trapping peer, and `kill` is
  untrappable.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TInc | TQuery | TExit
    type TagList = TNil | TCons(Tag, TagList)
    type Accepted indices (t: Tag)
      AccInc   : Accepted(TInc)
      AccQuery : Accepted(TQuery)
      AccExit  : Accepted(TExit)
    type AllAccepted indices (ts: TagList)
      AANil  : AllAccepted(TNil)
      AACons : Accepted(t) -> AllAccepted(rest) -> AllAccepted(TCons(t, rest))
    type Trap = Trapping | NotTrapping
    type Reason = Normal | Abnormal | Kill
    type Proc = Alive(TagList, TagList, Trap) | Dead
    type WTP indices (p: Proc)
      WTAlive : AllAccepted(e) -> AllAccepted(m) -> WTP(Alive(e, m, tr))
      WTDead  : WTP(Dead)
    type Step indices (r: Reason, before: Proc, after: Proc)
      SNormalTrap    : Accepted(TExit) -> Step(Normal, Alive(e, m, Trapping), Alive(TCons(TExit, e), m, Trapping))
      SNormalSurvive : Step(Normal, Alive(e, m, NotTrapping), Alive(e, m, NotTrapping))
      SAbnormalTrap  : Accepted(TExit) -> Step(Abnormal, Alive(e, m, Trapping), Alive(TCons(TExit, e), m, Trapping))
      SAbnormalProp  : Step(Abnormal, Alive(e, m, NotTrapping), Dead)
      SKillTrap      : Step(Kill, Alive(e, m, Trapping), Dead)
      SKillNoTrap    : Step(Kill, Alive(e, m, NotTrapping), Dead)
    fn preservation({r: Reason}, {b: Proc}, {a: Proc}, wt: WTP(b), s: Step(r, b, a)) -> WTP(a) = match s
      SNormalTrap(accexit) -> match wt
        WTAlive(ae, am) -> WTAlive(AACons(accexit, ae), am)
      SNormalSurvive() -> wt
      SAbnormalTrap(accexit) -> match wt
        WTAlive(ae, am) -> WTAlive(AACons(accexit, ae), am)
      SAbnormalProp() -> WTDead
      SKillTrap()   -> WTDead
      SKillNoTrap() -> WTDead
  """

  defp verdict(defs) do
    case Program.elaborate("mod ExitT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a normal exit leaves a non-trapping peer alive (the survive step)" do
    defs = """
      fn survive() -> Step(Normal, Alive(TNil, TNil, NotTrapping), Alive(TNil, TNil, NotTrapping)) =
        SNormalSurvive()
    """

    assert verdict(defs) == :accept
  end

  test "a normal exit CANNOT kill a non-trapping peer (no step reaches Dead under Normal)" do
    # SNormalSurvive keeps it Alive; SAbnormalProp/SKillNoTrap reach Dead but under a DIFFERENT
    # reason. So Step(Normal, Alive(.., NotTrapping), Dead) is uninhabited.
    defs = """
      fn bad() -> Step(Normal, Alive(TNil, TNil, NotTrapping), Dead) = SAbnormalProp()
    """

    assert verdict(defs) == :reject
  end

  test "kill is untrappable: it kills even a trapping peer" do
    defs = """
      fn killed() -> Step(Kill, Alive(TNil, TNil, Trapping), Dead) = SKillTrap()
    """

    assert verdict(defs) == :accept
  end

  test "an abnormal exit propagates a non-trapping peer to Dead" do
    defs = """
      fn propagates() -> Step(Abnormal, Alive(TNil, TNil, NotTrapping), Dead) = SAbnormalProp()
    """

    assert verdict(defs) == :accept
  end
end
