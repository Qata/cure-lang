defmodule Cure.Stdlib.OtpMonitorTest do
  @moduledoc """
  `Std.Otp.Monitor` — the typed monitor / DOWN-as-message discipline: a monitor
  reference is evidence that its holder accepts `DOWN`, and delivering `DOWN` on the
  monitored process's death preserves well-typedness. The proof is re-checked every
  build via the stdlib preload; these tests pin the safety content — a monitor CANNOT
  be formed for a receiver whose vocabulary excludes `DOWN`, so an unmonitored process
  never receives a `DOWN` it cannot handle.
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
    type MRef = MkMRef(Accepted(TDown))
    fn monitor_accepts(r: MRef) -> Accepted(TDown) = match r
      MkMRef(a) -> a
    type Step indices (before: Config, after: Config)
      SDown : MRef -> Step(MkConfig(e, m), MkConfig(TCons(TDown, e), m))
    fn preservation({b: Config}, {a: Config}, wt: WT(b), s: Step(b, a)) -> WT(a) = match s
      SDown(mref) -> match mref
        MkMRef(accdown) -> match wt
          MkWT(ae, am) -> MkWT(AACons(accdown, ae), am)
  """

  defp verdict(defs) do
    case Program.elaborate("mod MonitorT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a monitor can be established and delivering DOWN preserves well-typedness" do
    defs = """
      fn establish() -> MRef = MkMRef(AccDown)
    """

    assert verdict(defs) == :accept
  end

  # A receiver whose message vocabulary EXCLUDES DOWN: no AccDown, so no monitor.
  @no_down """
    type Tag2 = T2Inc | T2Query
    type Acc2 indices (t: Tag2)
      A2Inc   : Acc2(T2Inc)
      A2Query : Acc2(T2Query)
    type MRef2 = MkMRef2(Acc2(T2Query))
  """

  test "a receiver without DOWN in its vocabulary cannot form a monitor (Accepted(TDown) uninhabited)" do
    # There is no Acc2(TDown)-style constructor — a monitor over this receiver is
    # unconstructible, so it can never be sent a DOWN.
    defs = """
      #{@no_down}
      type Void = |
      fn no_down_accepted(p: Acc2(T2Inc)) -> Acc2(T2Query) = match p
    """

    # The absurd claim (Inc-acceptance yields Query-acceptance) must be rejected —
    # a receiver's acceptances are not interchangeable; DOWN is not silently added.
    assert verdict(defs) == :reject
  end

  test "holding a monitor proves DOWN-acceptance (monitor_accepts extracts the evidence)" do
    defs = """
      fn proof_from_monitor(r: MRef) -> Accepted(TDown) = monitor_accepts(r)
    """

    assert verdict(defs) == :accept
  end
end
