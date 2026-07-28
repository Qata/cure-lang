defmodule Cure.Stdlib.OtpSystemTest do
  @moduledoc """
  `Std.Otp.System` — subject reduction under INTERLEAVING: a pool of concurrent
  processes, where any one process may step while the others stay fixed, preserves
  global well-typedness. The proof is re-checked every build via the stdlib preload;
  these tests pin the safety content — a concrete two-process system steps and stays
  globally well-typed, and the excluded tag `TDec` still cannot be held by any process.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TInc | TDec | TQuery
    type TagList = TNil | TCons(Tag, TagList)
    type Accepted indices (t: Tag)
      AccInc   : Accepted(TInc)
      AccQuery : Accepted(TQuery)
    type AllAccepted indices (ts: TagList)
      AANil  : AllAccepted(TNil)
      AACons : Accepted(t) -> AllAccepted(rest) -> AllAccepted(TCons(t, rest))
    type Config = MkConfig(TagList, TagList)
    type WT indices (c: Config)
      MkWT : AllAccepted(e) -> AllAccepted(m) -> WT(MkConfig(e, m))
    type Step indices (before: Config, after: Config)
      SSend   : Accepted(t) -> Step(MkConfig(e, m), MkConfig(TCons(t, e), m))
      SArrive : Step(MkConfig(TCons(t, e), m), MkConfig(e, TCons(t, m)))
      SRecv   : Step(MkConfig(e, TCons(t, m)), MkConfig(e, m))
    fn preservation({b: Config}, {a: Config}, wt: WT(b), s: Step(b, a)) -> WT(a) = match s
      SSend(acc) -> match wt
        MkWT(ae, am) -> MkWT(AACons(acc, ae), am)
      SArrive() -> match wt
        MkWT(ae, am) -> match ae
          AACons(at, ae2) -> MkWT(ae2, AACons(at, am))
      SRecv() -> match wt
        MkWT(ae, am) -> match am
          AACons(rat, am2) -> MkWT(ae, am2)
    type System = SNil | SCons(Config, System)
    type WTSys indices (sys: System)
      WSNil  : WTSys(SNil)
      WSCons : WT(c) -> WTSys(rest) -> WTSys(SCons(c, rest))
    type SysStep indices (before: System, after: System)
      StepHere  : Step(c, c2) -> SysStep(SCons(c, rest), SCons(c2, rest))
      StepThere : SysStep(rest, rest2) -> SysStep(SCons(c, rest), SCons(c, rest2))
    fn sys_preservation({b: System}, {a: System}, wt: WTSys(b), s: SysStep(b, a)) -> WTSys(a) = match s
      StepHere(step) -> match wt
        WSCons(wtc, wrest) -> WSCons(preservation(wtc, step), wrest)
      StepThere(s2) -> match wt
        WSCons(wtc, wrest) -> WSCons(wtc, sys_preservation(wrest, s2))
  """

  defp verdict(defs) do
    case Program.elaborate("mod SystemT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a concrete well-typed two-process system type-checks" do
    defs = """
      fn two() -> WTSys(SCons(MkConfig(TCons(TInc, TNil), TNil), SCons(MkConfig(TNil, TCons(TQuery, TNil)), SNil))) =
        WSCons(MkWT(AACons(AccInc, AANil), AANil), WSCons(MkWT(AANil, AACons(AccQuery, AANil)), WSNil))
    """

    assert verdict(defs) == :accept
  end

  test "the excluded tag TDec cannot be held by a process in the system" do
    defs = """
      fn bad() -> WTSys(SCons(MkConfig(TNil, TCons(TDec, TNil)), SNil)) =
        WSCons(MkWT(AANil, AACons(AccInc, AANil)), WSNil)
    """

    assert verdict(defs) == :reject
  end
end
