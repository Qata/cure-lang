defmodule Cure.Stdlib.OtpHetRoutingTest do
  @moduledoc """
  `Std.Otp.HetRouting` — heterogeneous typed routing: each process has its own
  accepted-set (interface), and a message may only be routed to a process that accepts
  it, preserving global well-typedness. The proof is re-checked every build via the
  stdlib preload; these tests pin the safety content — routing a message into a process
  whose interface excludes it is unconstructible.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TInc | TDec | TQuery
    type TagList = TNil | TCons(Tag, TagList)
    type Member indices (t: Tag, set: TagList)
      MemHere  : Member(t, TCons(t, rest))
      MemThere : Member(t, rest) -> Member(t, TCons(y, rest))
    type AllMember indices (ts: TagList, set: TagList)
      AMNil  : AllMember(TNil, set)
      AMCons : Member(t, set) -> AllMember(rest, set) -> AllMember(TCons(t, rest), set)
    type Proc = MkProc(TagList, TagList, TagList)
    type WTProc indices (p: Proc)
      MkWTP : AllMember(e, set) -> AllMember(m, set) -> WTProc(MkProc(set, e, m))
    type System = SNil | SCons(Proc, System)
    type WTSys indices (sys: System)
      WSNil  : WTSys(SNil)
      WSCons : WTProc(p) -> WTSys(rest) -> WTSys(SCons(p, rest))
    type Deliver indices (before: System, after: System)
      DHere  : Member(t, set) -> Deliver(SCons(MkProc(set, e, m), rest), SCons(MkProc(set, TCons(t, e), m), rest))
      DThere : Deliver(rest, rest2) -> Deliver(SCons(p, rest), SCons(p, rest2))
    fn preservation({b: System}, {a: System}, wt: WTSys(b), d: Deliver(b, a)) -> WTSys(a) = match d
      DHere(mem) -> match wt
        WSCons(wtp, wrest) -> match wtp
          MkWTP(ame, amm) -> WSCons(MkWTP(AMCons(mem, ame), amm), wrest)
      DThere(d2) -> match wt
        WSCons(wtp, wrest) -> WSCons(wtp, preservation(wrest, d2))
  """

  defp verdict(defs) do
    case Program.elaborate("mod HetRoutingT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "TInc is a member of an interface [TInc, TQuery]" do
    defs = """
      fn inc_member() -> Member(TInc, TCons(TInc, TCons(TQuery, TNil))) = MemHere()
      fn query_member() -> Member(TQuery, TCons(TInc, TCons(TQuery, TNil))) = MemThere(MemHere())
    """

    assert verdict(defs) == :accept
  end

  test "a tag NOT in an interface has no membership witness" do
    # TDec is not in [TInc, TQuery], so Member(TDec, [TInc, TQuery]) is uninhabited.
    defs = """
      fn bad() -> Member(TDec, TCons(TInc, TCons(TQuery, TNil))) = MemThere(MemHere())
    """

    assert verdict(defs) == :reject
  end
end
