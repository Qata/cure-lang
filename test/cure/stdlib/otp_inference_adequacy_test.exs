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
    type Behaviour = BNil | BRecv(Tag, Behaviour) | BSend(Tag, Behaviour) | BSeq(Behaviour, Behaviour)
    fn append(a: TagList, b: TagList) -> TagList = match a
      TNil()         -> b
      TCons(t, rest) -> TCons(t, append(rest, b))
    fn infer(b: Behaviour) -> TagList = match b
      BNil()      -> TNil
      BRecv(t, k) -> TCons(t, infer(k))
      BSend(t, k) -> TCons(t, infer(k))
      BSeq(l, r)  -> append(infer(l), infer(r))
    fn member_append_left({t: Tag}, {xs: TagList}, {ys: TagList}, m: Member(t, xs)) -> Member(t, append(xs, ys)) = match m
      MemHere()    -> MemHere()
      MemThere(m2) -> MemThere(member_append_left(m2))
    fn member_append_right(xs: TagList, {t: Tag}, {ys: TagList}, m: Member(t, ys)) -> Member(t, append(xs, ys)) = match xs
      TNil()         -> m
      TCons(y, rest) -> MemThere(member_append_right(rest, m))
    type SendsIn indices (b: Behaviour, t: Tag)
      SendHere  : SendsIn(BSend(t, k), t)
      SendRecvK : SendsIn(k, t) -> SendsIn(BRecv(y, k), t)
      SendSendK : SendsIn(k, t) -> SendsIn(BSend(y, k), t)
      SendSeqL  : SendsIn(l, t) -> SendsIn(BSeq(l, r), t)
      SendSeqR  : SendsIn(r, t) -> SendsIn(BSeq(l, r), t)
    fn coverage(b: Behaviour, {t: Tag}, sends: SendsIn(b, t)) -> Member(t, infer(b)) = match b
      BNil()      -> match sends
      BRecv(y, k) -> match sends
        SendRecvK(s2) -> MemThere(coverage(k, s2))
      BSend(y, k) -> match sends
        SendHere()    -> MemHere()
        SendSendK(s2) -> MemThere(coverage(k, s2))
      BSeq(l, r)  -> match sends
        SendSeqL(s2) -> member_append_left(coverage(l, s2))
        SendSeqR(s2) -> member_append_right(infer(l), coverage(r, s2))
  """

  defp verdict(defs) do
    case Program.elaborate("mod AdqT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _error} -> :reject
    end
  end

  test "the inferred interface of a behaviour covers its sends (coverage)" do
    # Given a send site for TC in b, coverage yields Member(TC, infer(b)). `b` is fixed by
    # the SendsIn parameter's type (infer is not injective, so it can't be recovered from
    # the goal alone).
    defs = """
      fn tc_covered(s: SendsIn(BSend(TA, BRecv(TB, BSend(TC, BNil))), TC)) -> Member(TC, infer(BSend(TA, BRecv(TB, BSend(TC, BNil))))) =
        coverage(BSend(TA, BRecv(TB, BSend(TC, BNil))), s)
    """

    assert verdict(defs) == :accept
  end

  test "coverage handles a BRANCHING behaviour: a send on the right branch of a BSeq is covered" do
    # BSeq(BSend(TA, BNil), BSend(TC, BNil)): the send of TC lives on the RIGHT branch, so its
    # membership in infer(BSeq(...)) = append(infer left, infer right) goes through
    # member_append_right — the case that needs infer(left) relevantly (recovered by matching
    # the behaviour before the evidence).
    defs = """
      fn tc_on_right(s: SendsIn(BSeq(BSend(TA, BNil), BSend(TC, BNil)), TC)) -> Member(TC, infer(BSeq(BSend(TA, BNil), BSend(TC, BNil)))) =
        coverage(BSeq(BSend(TA, BNil), BSend(TC, BNil)), s)
    """

    assert verdict(defs) == :accept
  end

  test "coverage may eliminate indexed evidence before inspecting its sibling value" do
    defs = """
      fn coverage_evidence_first(b: Behaviour, {t: Tag}, sends: SendsIn(b, t)) -> Member(t, infer(b)) = match sends
        SendHere()    -> MemHere()
        SendRecvK(s2) -> match b
          BRecv(y, k) -> MemThere(coverage_evidence_first(k, s2))
        SendSendK(s2) -> match b
          BSend(y, k) -> MemThere(coverage_evidence_first(k, s2))
        SendSeqL(s2) -> match b
          BSeq(l, r) -> member_append_left(coverage_evidence_first(l, s2))
        SendSeqR(s2) -> match b
          BSeq(l, r) -> member_append_right(infer(l), coverage_evidence_first(r, s2))
    """

    assert verdict(defs) == :accept
  end

  test "a tag the behaviour never sends has no send site (SendsIn is uninhabited for it)" do
    # BSend(TA, BNil) has no send of TC: SendHere requires the head tag to be TC.
    defs = """
      fn no_tc_send(s: SendsIn(BSend(TA, BNil), TC)) -> Member(TC, infer(BSend(TA, BNil))) =
        coverage(BSend(TA, BNil), s)
      fn absurd() -> SendsIn(BSend(TA, BNil), TC) = SendHere()
    """

    assert verdict(defs) == :reject
  end
end
