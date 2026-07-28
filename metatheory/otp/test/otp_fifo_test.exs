defmodule Cure.Stdlib.OtpFifoTest do
  @moduledoc """
  `Std.Otp.Fifo` — FIFO-faithful mailbox ordering: `SArrive` appends to the mailbox
  END, and preservation is re-proved via the `all_accepted_snoc` lemma (appending an
  accepted message keeps the mailbox all-accepted). The proof is re-checked every build
  via the stdlib preload; these tests pin the snoc lemma and the excluded-tag exclusion
  under FIFO delivery.
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
    fn snoc(ts: TagList, t: Tag) -> TagList = match ts
      TNil()         -> TCons(t, TNil)
      TCons(h, rest) -> TCons(h, snoc(rest, t))
    fn all_accepted_snoc({ts: TagList}, {t: Tag}, all: AllAccepted(ts), acc: Accepted(t)) -> AllAccepted(snoc(ts, t)) = match all
      AANil()           -> AACons(acc, AANil)
      AACons(ah, arest) -> AACons(ah, all_accepted_snoc(arest, acc))
    type Config = MkConfig(TagList, TagList)
    type WT indices (c: Config)
      MkWT : AllAccepted(e) -> AllAccepted(m) -> WT(MkConfig(e, m))
    type Step indices (before: Config, after: Config)
      SSend   : Accepted(t) -> Step(MkConfig(e, m), MkConfig(TCons(t, e), m))
      SArrive : Step(MkConfig(TCons(t, e), m), MkConfig(e, snoc(m, t)))
      SRecv   : Step(MkConfig(e, TCons(t, m)), MkConfig(e, m))
    fn preservation({b: Config}, {a: Config}, wt: WT(b), s: Step(b, a)) -> WT(a) = match s
      SSend(acc) -> match wt
        MkWT(ae, am) -> MkWT(AACons(acc, ae), am)
      SArrive() -> match wt
        MkWT(ae, am) -> match ae
          AACons(at, ae2) -> MkWT(ae2, all_accepted_snoc(am, at))
      SRecv() -> match wt
        MkWT(ae, am) -> match am
          AACons(rat, am2) -> MkWT(ae, am2)
  """

  defp verdict(defs) do
    case Program.elaborate("mod FifoT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "appending an accepted message to a mailbox is well-typed (snoc lemma witnessed)" do
    defs = """
      fn append_ok() -> AllAccepted(snoc(TCons(TQuery, TNil), TInc)) =
        all_accepted_snoc(AACons(AccQuery, AANil), AccInc)
    """

    assert verdict(defs) == :accept
  end

  test "the excluded tag TDec still cannot be held under FIFO delivery" do
    defs = """
      fn bad() -> WT(MkConfig(TNil, TCons(TDec, TNil))) =
        MkWT(AANil, AACons(AccInc, AANil))
    """

    assert verdict(defs) == :reject
  end
end
