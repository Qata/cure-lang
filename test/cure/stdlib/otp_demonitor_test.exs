defmodule Cure.Stdlib.OtpDemonitorTest do
  @moduledoc """
  `Std.Otp.Demonitor` — monitor cancellation: a `MRef` is indexed by an
  `Active`/`Removed` state, `demonitor` moves `Active -> Removed`, and the death step
  `SDown` requires an `Active` monitor. The proof is re-checked every build via the
  stdlib preload; these tests pin the safety content — a DOWN cannot be delivered
  through a removed monitor.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TInc | TQuery | TDown
    type TagList = TNil | TCons(Tag, TagList)
    type Accepted indices (t: Tag)
      AccInc   : Accepted(TInc)
      AccQuery : Accepted(TQuery)
      AccDown  : Accepted(TDown)
    type AllAccepted indices (ts: TagList)
      AANil  : AllAccepted(TNil)
      AACons : Accepted(t) -> AllAccepted(rest) -> AllAccepted(TCons(t, rest))
    type Config = MkConfig(TagList, TagList)
    type WT indices (c: Config)
      MkWT : AllAccepted(e) -> AllAccepted(m) -> WT(MkConfig(e, m))
    type MState = Active | Removed
    type MRef indices (s: MState)
      MkMRef : Accepted(TDown) -> MRef(Active)
      Gone   : MRef(Removed)
    fn demonitor(r: MRef(Active)) -> MRef(Removed) = Gone
    type Step indices (before: Config, after: Config)
      SDown : MRef(Active) -> Step(MkConfig(e, m), MkConfig(TCons(TDown, e), m))
    fn preservation({b: Config}, {a: Config}, wt: WT(b), s: Step(b, a)) -> WT(a) = match s
      SDown(mref) -> match mref
        MkMRef(accdown) -> match wt
          MkWT(ae, am) -> MkWT(AACons(accdown, ae), am)
  """

  defp verdict(defs) do
    case Program.elaborate("mod DemonT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a monitor can be established and demonitored" do
    defs = """
      fn establish() -> MRef(Active) = MkMRef(AccDown)
      fn cancel(r: MRef(Active)) -> MRef(Removed) = demonitor(r)
    """

    assert verdict(defs) == :accept
  end

  test "a DOWN cannot be delivered through a removed monitor (SDown requires Active)" do
    defs = """
      fn bad({e: TagList}, {m: TagList}, r: MRef(Removed)) -> Step(MkConfig(e, m), MkConfig(TCons(TDown, e), m)) =
        SDown(r)
    """

    assert verdict(defs) == :reject
  end
end
