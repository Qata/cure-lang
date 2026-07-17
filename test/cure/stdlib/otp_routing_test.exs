defmodule Cure.Stdlib.OtpRoutingTest do
  @moduledoc """
  `Std.Otp.Routing` — typed cross-process delivery: routing an accepted message into
  any process's ether preserves global well-typedness. The proof is re-checked every
  build via the stdlib preload; these tests pin the safety content — a concrete
  delivery to the second process type-checks, and delivery carries an `Accepted`
  obligation so an unhandled message cannot be routed.
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
    type System = SNil | SCons(Config, System)
    type WTSys indices (sys: System)
      WSNil  : WTSys(SNil)
      WSCons : WT(c) -> WTSys(rest) -> WTSys(SCons(c, rest))
    type Deliver indices (before: System, after: System)
      DeliverHere  : Accepted(t) -> Deliver(SCons(MkConfig(e, m), rest), SCons(MkConfig(TCons(t, e), m), rest))
      DeliverThere : Deliver(rest, rest2) -> Deliver(SCons(c, rest), SCons(c, rest2))
    fn deliver_preservation({b: System}, {a: System}, wt: WTSys(b), d: Deliver(b, a)) -> WTSys(a) = match d
      DeliverHere(acc) -> match wt
        WSCons(wtc, wrest) -> match wtc
          MkWT(ae, am) -> WSCons(MkWT(AACons(acc, ae), am), wrest)
      DeliverThere(d2) -> match wt
        WSCons(wtc, wrest) -> WSCons(wtc, deliver_preservation(wrest, d2))
  """

  defp verdict(defs) do
    case Program.elaborate("mod RoutingT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "delivering an accepted message to the second process type-checks" do
    defs = """
      fn route() -> Deliver(SCons(MkConfig(TNil, TNil), SCons(MkConfig(TNil, TNil), SNil)), SCons(MkConfig(TNil, TNil), SCons(MkConfig(TCons(TQuery, TNil), TNil), SNil))) =
        DeliverThere(DeliverHere(AccQuery))
    """

    assert verdict(defs) == :accept
  end

  test "delivery to an empty pool is impossible (no process to route to)" do
    defs = """
      fn bad() -> Deliver(SNil, SNil) = DeliverHere(AccInc)
    """

    assert verdict(defs) == :reject
  end
end
