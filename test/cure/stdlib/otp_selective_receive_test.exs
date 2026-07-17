defmodule Cure.Stdlib.OtpSelectiveReceiveTest do
  @moduledoc """
  `Std.Otp.SelectiveReceive` — ordered selective receive (a slice of G8): a `SelRecv`
  scans the mailbox in arrival order and consumes the first matching tag; selective
  receive preserves well-typedness and the received message is accepted. The proof is
  re-checked every build via the stdlib preload; these tests pin the safety content —
  the scan respects order, and receiving a tag absent from the mailbox is impossible.
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
    type SelRecv indices (before: TagList, x: Tag, after: TagList)
      SelHere : SelRecv(TCons(x, rest), x, rest)
      SelSkip : SelRecv(rest, x, rest2) -> SelRecv(TCons(y, rest), x, TCons(y, rest2))
    fn preserves({x: Tag}, {before: TagList}, {after: TagList}, all: AllAccepted(before), s: SelRecv(before, x, after)) -> AllAccepted(after) = match s
      SelHere() -> match all
        AACons(accx, rest_acc) -> rest_acc
      SelSkip(s2) -> match all
        AACons(accy, rest_acc) -> AACons(accy, preserves(rest_acc, s2))
    fn received_accepted({x: Tag}, {before: TagList}, {after: TagList}, all: AllAccepted(before), s: SelRecv(before, x, after)) -> Accepted(x) = match s
      SelHere() -> match all
        AACons(accx, rest_acc) -> accx
      SelSkip(s2) -> match all
        AACons(accy, rest_acc) -> received_accepted(rest_acc, s2)
  """

  defp verdict(defs) do
    case Program.elaborate("mod SelRecvT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the proofs and an order-respecting selective receive (skip TInc, take TQuery) type-check" do
    defs = """
      fn example() -> SelRecv(TCons(TInc, TCons(TQuery, TNil)), TQuery, TCons(TInc, TNil)) =
        SelSkip(SelHere())
    """

    assert verdict(defs) == :accept
  end

  test "receiving a tag NOT in the mailbox is impossible" do
    # TQuery is not present in [TInc], so no SelRecv([TInc], TQuery, _) exists.
    defs = """
      fn bad() -> SelRecv(TCons(TInc, TNil), TQuery, TNil) = SelHere()
    """

    assert verdict(defs) == :reject
  end

  test "the scan respects order: taking the head keeps the tail" do
    defs = """
      fn head_first() -> SelRecv(TCons(TQuery, TCons(TInc, TNil)), TQuery, TCons(TInc, TNil)) =
        SelHere()
    """

    assert verdict(defs) == :accept
  end
end
