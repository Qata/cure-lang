defmodule Cure.Stdlib.OtpReplyPreservationTest do
  @moduledoc """
  `Std.Otp.ReplyPreservation` — the COMPOSE of obligation (1)'s per-request dependent
  `ReplyOf` typing (`Std.Otp.Proof`) with the Core Erlang send/arrive/receive reduction
  (`Std.Otp.Preservation`): the dependent reply typing is preserved through delivery.
  The proof and the `reify` bridge are re-checked every build via the stdlib preload;
  these tests pin the *safety content* — a wrong-typed reply is unrepresentable and no
  well-typed config can carry one — and guard the proof against becoming vacuous.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # The self-contained reply calculus (mirrors metatheory/otp/src/otp_reply_preservation.cure), so
  # the tests can add well-typed and ILL-typed configs/bridges against it.
  @calculus """
    type Req = GetCount | Ping
    type Val = VInt | VAtom
    type HasReply indices (r: Req, v: Val)
      HRGet  : HasReply(GetCount, VInt)
      HRPing : HasReply(Ping, VAtom)
    type Reply = MkReply(Req, Val)
    type Replies = RNil | RCons(Reply, Replies)
    type AllReplied indices (rs: Replies)
      ARNil  : AllReplied(RNil)
      ARCons : HasReply(r, v) -> AllReplied(rest) -> AllReplied(RCons(MkReply(r, v), rest))
    type Config = MkConfig(Replies, Replies)
    type WT indices (c: Config)
      MkWT : AllReplied(e) -> AllReplied(m) -> WT(MkConfig(e, m))
    type Step indices (before: Config, after: Config)
      SReply  : HasReply(r, v) -> Step(MkConfig(e, m), MkConfig(RCons(MkReply(r, v), e), m))
      SArrive : Step(MkConfig(RCons(MkReply(r, v), e), m), MkConfig(e, RCons(MkReply(r, v), m)))
      SRecv   : Step(MkConfig(e, RCons(MkReply(r, v), m)), MkConfig(e, m))
    fn preservation({b: Config}, {a: Config}, wt: WT(b), s: Step(b, a)) -> WT(a) = match s
      SReply(hr) -> match wt
        MkWT(ae, am) -> MkWT(ARCons(hr, ae), am)
      SArrive() -> match wt
        MkWT(ae, am) -> match ae
          ARCons(hr, ae2) -> MkWT(ae2, ARCons(hr, am))
      SRecv() -> match wt
        MkWT(ae, am) -> match am
          ARCons(hr, am2) -> MkWT(ae, am2)
    type RInt  = RI
    type RAtom = RA
    fn ReplyOf(r: Req) -> Type = match r
      GetCount() -> RInt
      Ping()     -> RAtom
    fn reify({r: Req}, {v: Val}, hr: HasReply(r, v)) -> ReplyOf(r) = match hr
      HRGet()  -> RI
      HRPing() -> RA
  """

  defp verdict(defs) do
    case Program.elaborate("mod ReplyPres\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the preservation proof, the ReplyOf bridge, and a non-vacuous config type-check" do
    defs = """
      fn example() -> WT(MkConfig(RCons(MkReply(GetCount, VInt), RNil), RNil)) =
        MkWT(ARCons(HRGet, ARNil), ARNil)
    """

    assert verdict(defs) == :accept
  end

  test "a wrong-typed reply HasReply(GetCount, VAtom) is uninhabited (absurd match)" do
    defs = """
      type Void = |
      fn wrong_reply(p: HasReply(GetCount, VAtom)) -> Void = match p
    """

    assert verdict(defs) == :accept
  end

  test "a config that HOLDS a wrong-typed reply cannot be well-typed" do
    # No HasReply(GetCount, VAtom) exists, so the ARCons witness is unbuildable.
    defs = """
      fn bad() -> WT(MkConfig(RCons(MkReply(GetCount, VAtom), RNil), RNil)) =
        MkWT(ARCons(HRGet, ARNil), ARNil)
    """

    assert verdict(defs) == :reject
  end

  test "the ReplyOf bridge is faithful: reify cannot return the wrong reply type" do
    # HRGet answers GetCount, whose ReplyOf is RInt; returning RAtom (RA) must reject.
    defs = """
      fn reify_bad({r: Req}, {v: Val}, hr: HasReply(r, v)) -> ReplyOf(r) = match hr
        HRGet()  -> RA
        HRPing() -> RA
    """

    assert verdict(defs) == :reject
  end
end
