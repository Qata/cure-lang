defmodule Cure.Stdlib.OtpUnlinkTest do
  @moduledoc """
  `Std.Otp.Unlink` — link cancellation: a `LinkRef` is indexed by a `Linked`/`Unlinked`
  state, `unlink` moves `Linked -> Unlinked`, and the peer-death step (`SExitTrap`/`SExitProp`)
  requires a `Linked` ref. The proof is re-checked every build via the stdlib preload; these
  tests pin the safety content — after `unlink`, neither an EXIT message nor death propagation
  can be delivered through the severed link.
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
    type LState = Linked | Unlinked
    type LinkRef indices (s: LState)
      LinkedTrap   : Accepted(TExit) -> LinkRef(Linked)
      LinkedNoTrap : LinkRef(Linked)
      Severed      : LinkRef(Unlinked)
    fn unlink(l: LinkRef(Linked)) -> LinkRef(Unlinked) = Severed
    type Step indices (before: Proc, after: Proc)
      SExitTrap : LinkRef(Linked) -> Accepted(TExit) -> Step(Alive(e, m, Trapping), Alive(TCons(TExit, e), m, Trapping))
      SExitProp : LinkRef(Linked) -> Step(Alive(e, m, NotTrapping), Dead)
    fn preservation({b: Proc}, {a: Proc}, wt: WTP(b), s: Step(b, a)) -> WTP(a) = match s
      SExitTrap(lref, accexit) -> match wt
        WTAlive(ae, am) -> WTAlive(AACons(accexit, ae), am)
      SExitProp(lref) -> WTDead
  """

  defp verdict(defs) do
    case Program.elaborate("mod UnlinkT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a link can be established and unlinked" do
    defs = """
      fn establish() -> LinkRef(Linked) = LinkedTrap(AccExit)
      fn cancel(l: LinkRef(Linked)) -> LinkRef(Unlinked) = unlink(l)
    """

    assert verdict(defs) == :accept
  end

  test "an EXIT message cannot be delivered through a severed link (SExitTrap requires Linked)" do
    defs = """
      fn bad({e: TagList}, {m: TagList}, l: LinkRef(Unlinked), a: Accepted(TExit)) -> Step(Alive(e, m, Trapping), Alive(TCons(TExit, e), m, Trapping)) =
        SExitTrap(l, a)
    """

    assert verdict(defs) == :reject
  end

  test "death propagation cannot fire through a severed link (SExitProp requires Linked)" do
    defs = """
      fn bad({e: TagList}, {m: TagList}, l: LinkRef(Unlinked)) -> Step(Alive(e, m, NotTrapping), Dead) =
        SExitProp(l)
    """

    assert verdict(defs) == :reject
  end
end
