defmodule Cure.Stdlib.OtpPreservationTest do
  @moduledoc """
  `Std.Otp.Preservation` — subject reduction for the Core Erlang send/arrive/receive
  reduction (Bereczky et al. 2311.10482, Figs 3–5), proven in Cure. The proof itself
  is re-checked every build via the stdlib preload; these tests pin the *safety
  content* — the excluded tag can neither be sent nor held by a well-typed config —
  and guard the proof against becoming vacuous.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # The self-contained calculus (mirrors lib/std/otp_preservation.cure), so the tests
  # can add well-typed and ILL-typed clients against it.
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
  """

  defp verdict(defs) do
    case Program.elaborate("mod Pres\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the preservation proof and a non-vacuous well-typed config type-check" do
    defs = """
      fn example() -> WT(MkConfig(TCons(TInc, TNil), TCons(TQuery, TNil))) =
        MkWT(AACons(AccInc, AANil), AACons(AccQuery, AANil))
    """

    assert verdict(defs) == :accept
  end

  test "the excluded tag TDec is unaccepted (absurd match proves it uninhabited)" do
    defs = """
      type Void = |
      fn tdec_unaccepted(p: Accepted(TDec)) -> Void = match p
    """

    assert verdict(defs) == :accept
  end

  test "a config that HOLDS the excluded TDec cannot be well-typed" do
    defs = """
      fn bad() -> WT(MkConfig(TNil, TCons(TDec, TNil))) =
        MkWT(AANil, AACons(AccInc, AANil))
    """

    assert verdict(defs) == :reject
  end

  test "no SSend can introduce the excluded TDec into the ether" do
    # `send` demands an `Accepted(t)` proof; there is none for TDec, so a step that
    # would put TDec in flight is unconstructible.
    defs = """
      fn bad_send({e: TagList}, {m: TagList}) -> Step(MkConfig(e, m), MkConfig(TCons(TDec, e), m)) =
        SSend(AccInc)
    """

    assert verdict(defs) == :reject
  end
end
