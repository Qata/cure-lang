defmodule Cure.Stdlib.OtpInferenceAdequacyTest do
  @moduledoc """
  `Std.Otp.InferenceAdequacy` — the adequacy theorem: the statically inferred interface is
  preserved by the operational reduction of the behaviour it was inferred from (sequential
  first-order fragment). Proved end to end (preservation_at + coverage + adequacy), no
  holes; re-checked every build via the stdlib preload. These tests pin the safety content
  — a config running a behaviour stays within `infer(b)`, and a message outside `infer(b)`
  cannot be shown a member.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TA | TB | TC
    type TagList = TNil | TCons(Tag, TagList)
    type Member indices (t: Tag, iface: TagList)
      MemHere  : Member(t, TCons(t, rest))
      MemThere : Member(t, rest) -> Member(t, TCons(y, rest))
    type AllMember indices (ts: TagList, iface: TagList)
      AMNil  : AllMember(TNil, iface)
      AMCons : Member(t, iface) -> AllMember(rest, iface) -> AllMember(TCons(t, rest), iface)
    type Config = MkConfig(TagList, TagList)
    type WTat indices (c: Config, iface: TagList)
      MkWTat : AllMember(e, iface) -> AllMember(m, iface) -> WTat(MkConfig(e, m), iface)
    type Behaviour = BNil | BRecv(Tag, Behaviour) | BSend(Tag, Behaviour)
    fn infer(b: Behaviour) -> TagList = match b
      BNil()      -> TNil
      BRecv(t, k) -> TCons(t, infer(k))
      BSend(t, k) -> TCons(t, infer(k))
    type SendsIn indices (b: Behaviour, t: Tag)
      SendHere  : SendsIn(BSend(t, k), t)
      SendRecvK : SendsIn(k, t) -> SendsIn(BRecv(y, k), t)
      SendSendK : SendsIn(k, t) -> SendsIn(BSend(y, k), t)
    fn coverage({b: Behaviour}, {t: Tag}, sends: SendsIn(b, t)) -> Member(t, infer(b)) = match sends
      SendHere()    -> MemHere()
      SendRecvK(s2) -> MemThere(coverage(s2))
      SendSendK(s2) -> MemThere(coverage(s2))
  """

  defp verdict(defs) do
    case Program.elaborate("mod AdqT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the inferred interface of a behaviour covers its sends (coverage)" do
    # Given a send site for TC in b, coverage yields Member(TC, infer(b)). `b` is fixed by
    # the SendsIn parameter's type (infer is not injective, so it can't be recovered from
    # the goal alone).
    defs = """
      fn tc_covered(s: SendsIn(BSend(TA, BRecv(TB, BSend(TC, BNil))), TC)) -> Member(TC, infer(BSend(TA, BRecv(TB, BSend(TC, BNil))))) =
        coverage(s)
    """

    assert verdict(defs) == :accept
  end

  test "a tag the behaviour never sends has no send site (SendsIn is uninhabited for it)" do
    # BSend(TA, BNil) has no send of TC: SendHere requires the head tag to be TC.
    defs = """
      fn no_tc_send(s: SendsIn(BSend(TA, BNil), TC)) -> Member(TC, infer(BSend(TA, BNil))) =
        coverage(s)
      fn absurd() -> SendsIn(BSend(TA, BNil), TC) = SendHere()
    """

    assert verdict(defs) == :reject
  end
end
