defmodule Cure.Stdlib.OtpSafetyTest do
  @moduledoc """
  `Std.Otp.Safety` — type safety (progress + preservation) for the Core Erlang
  send/arrive/receive reduction: a well-typed configuration is either final or steps
  to a well-typed configuration (never stuck, never ill-typed). The proof is
  re-checked every build via the stdlib preload; these tests pin the safety content —
  a concrete non-final config makes progress, and the excluded tag `TDec` can neither
  be held by a well-typed config nor sent.
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
    type Safe indices (c: Config)
      Done : Safe(MkConfig(TNil, TNil))
      Go   : (after: Config) -> Step(c, after) -> WT(after) -> Safe(c)
    fn safety(c: Config, wt: WT(c)) -> Safe(c) = match c
      MkConfig(e, m) -> match e
        TCons(t, e2) -> Go(MkConfig(e2, TCons(t, m)), SArrive(), preservation(wt, SArrive()))
        TNil() -> match m
          TCons(t, m2) -> Go(MkConfig(TNil, m2), SRecv(), preservation(wt, SRecv()))
          TNil() -> Done()
  """

  defp verdict(defs) do
    case Program.elaborate("mod SafetyT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the safety proof and a concrete non-final well-typed config type-check" do
    defs = """
      fn example() -> Safe(MkConfig(TCons(TInc, TNil), TNil)) =
        safety(MkConfig(TCons(TInc, TNil), TNil), MkWT(AACons(AccInc, AANil), AANil))
    """

    assert verdict(defs) == :accept
  end

  test "a config holding the excluded TDec cannot be well-typed (so safety cannot apply)" do
    defs = """
      fn bad() -> WT(MkConfig(TNil, TCons(TDec, TNil))) =
        MkWT(AANil, AACons(AccInc, AANil))
    """

    assert verdict(defs) == :reject
  end

  test "the final configuration is safe via Done" do
    defs = """
      fn final_safe() -> Safe(MkConfig(TNil, TNil)) = Done()
    """

    assert verdict(defs) == :accept
  end
end
