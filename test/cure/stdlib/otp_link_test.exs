defmodule Cure.Stdlib.OtpLinkTest do
  @moduledoc """
  `Std.Otp.Link` — typed links and the `trap_exit` dispatch: on a linked peer's death,
  a trapping process receives a well-typed `EXIT` message and a non-trapping process
  propagates to `Dead`; preservation holds for both. The proof is re-checked every
  build via the stdlib preload; these tests pin the safety content — a trapping link
  carries `EXIT`-acceptance, and the two step rules are gated on the trap flag.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TInc | TQuery | TExit
    type TagList = TNil | TCons(Tag, TagList)
    type Accepted indices (t: Tag)
      AccInc   : Accepted(TInc)
      AccQuery : Accepted(TQuery)
      AccExit  : Accepted(TExit)
    type AllAccepted indices (ts: TagList)
      AANil  : AllAccepted(TNil)
      AACons : Accepted(t) -> AllAccepted(rest) -> AllAccepted(TCons(t, rest))
    type Trap = Trapping | NotTrapping
    type Proc = Alive(TagList, TagList, Trap) | Dead
    type WTP indices (p: Proc)
      WTAlive : AllAccepted(e) -> AllAccepted(m) -> WTP(Alive(e, m, tr))
      WTDead  : WTP(Dead)
    type Link indices (tr: Trap)
      LinkTrap   : Accepted(TExit) -> Link(Trapping)
      LinkNoTrap : Link(NotTrapping)
    type Step indices (before: Proc, after: Proc)
      SExitTrap : Accepted(TExit) -> Step(Alive(e, m, Trapping), Alive(TCons(TExit, e), m, Trapping))
      SExitProp : Step(Alive(e, m, NotTrapping), Dead)
    fn preservation({b: Proc}, {a: Proc}, wt: WTP(b), s: Step(b, a)) -> WTP(a) = match s
      SExitTrap(accexit) -> match wt
        WTAlive(ae, am) -> WTAlive(AACons(accexit, ae), am)
      SExitProp() -> WTDead
    fn trap_accepts(l: Link(Trapping)) -> Accepted(TExit) = match l
      LinkTrap(a) -> a
  """

  defp verdict(defs) do
    case Program.elaborate("mod LinkT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "both a trapping and a non-trapping link can be established" do
    defs = """
      fn establish_trap() -> Link(Trapping) = LinkTrap(AccExit)
      fn establish_notrap() -> Link(NotTrapping) = LinkNoTrap
    """

    assert verdict(defs) == :accept
  end

  test "the trap-message step is gated to trapping processes (wrong-flag step is unconstructible)" do
    # SExitTrap only steps a Trapping process; claiming it for a NotTrapping process rejects.
    defs = """
      fn bad({e: TagList}, {m: TagList}) -> Step(Alive(e, m, NotTrapping), Alive(TCons(TExit, e), m, NotTrapping)) =
        SExitTrap(AccExit)
    """

    assert verdict(defs) == :reject
  end

  test "the propagation step is gated to non-trapping processes" do
    # SExitProp only steps a NotTrapping process to Dead; claiming it for Trapping rejects.
    defs = """
      fn bad2({e: TagList}, {m: TagList}) -> Step(Alive(e, m, Trapping), Dead) = SExitProp()
    """

    assert verdict(defs) == :reject
  end

  test "a trapping link proves EXIT-acceptance (trap_accepts extracts the evidence)" do
    defs = """
      fn proof_from_link(l: Link(Trapping)) -> Accepted(TExit) = trap_accepts(l)
    """

    assert verdict(defs) == :accept
  end
end
