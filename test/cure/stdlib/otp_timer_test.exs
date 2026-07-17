defmodule Cure.Stdlib.OtpTimerTest do
  @moduledoc """
  `Std.Otp.Timer` — typed timers (`send_after`/`cancel_timer`/`receive after`): only an
  accepted message can be scheduled, a `TimerRef` is indexed by a `Pending`/`Cancelled`
  lifecycle state, and only a `Pending` timer can fire. The proof is re-checked every
  build via the stdlib preload; these tests pin the safety content — a cancelled timer
  cannot fire, and firing delivers only an accepted message.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TInc | TQuery | TTimeout
    type TagList = TNil | TCons(Tag, TagList)
    type Accepted indices (t: Tag)
      AccInc     : Accepted(TInc)
      AccQuery   : Accepted(TQuery)
      AccTimeout : Accepted(TTimeout)
    type AllAccepted indices (ts: TagList)
      AANil  : AllAccepted(TNil)
      AACons : Accepted(t) -> AllAccepted(rest) -> AllAccepted(TCons(t, rest))
    type Config = MkConfig(TagList, TagList)
    type WT indices (c: Config)
      MkWT : AllAccepted(e) -> AllAccepted(m) -> WT(MkConfig(e, m))
    type TState = Pending | Cancelled
    type TimerRef indices (t: Tag, s: TState)
      MkTimer : Accepted(t) -> TimerRef(t, Pending)
      Killed  : TimerRef(t, Cancelled)
    fn cancel({t: Tag}, r: TimerRef(t, Pending)) -> TimerRef(t, Cancelled) = Killed()
    type Step indices (before: Config, after: Config)
      SFire : TimerRef(t, Pending) -> Step(MkConfig(e, m), MkConfig(TCons(t, e), m))
    fn preservation({b: Config}, {a: Config}, wt: WT(b), s: Step(b, a)) -> WT(a) = match s
      SFire(timer) -> match timer
        MkTimer(acc) -> match wt
          MkWT(ae, am) -> MkWT(AACons(acc, ae), am)
  """

  defp verdict(defs) do
    case Program.elaborate("mod TimerT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a timeout can be scheduled and cancelled" do
    defs = """
      fn schedule_timeout() -> TimerRef(TTimeout, Pending) = MkTimer(AccTimeout)
      fn kill(r: TimerRef(TTimeout, Pending)) -> TimerRef(TTimeout, Cancelled) = cancel(r)
    """

    assert verdict(defs) == :accept
  end

  test "a cancelled timer cannot fire (SFire requires Pending)" do
    # A step firing a Cancelled timer is unconstructible.
    defs = """
      fn bad_fire({e: TagList}, {m: TagList}, r: TimerRef(TTimeout, Cancelled)) -> Step(MkConfig(e, m), MkConfig(TCons(TTimeout, e), m)) =
        SFire(r)
    """

    assert verdict(defs) == :reject
  end

  test "firing delivers the scheduled message and preserves well-typedness" do
    defs = """
      fn fire_ok({e: TagList}, {m: TagList}, wt: WT(MkConfig(e, m))) -> WT(MkConfig(TCons(TTimeout, e), m)) =
        preservation(wt, SFire(MkTimer(AccTimeout)))
    """

    assert verdict(defs) == :accept
  end
end
