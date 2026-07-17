defmodule Cure.Stdlib.OtpInferenceLawsTest do
  @moduledoc """
  `Std.Otp.InferenceLaws` — the algebra of inferred interfaces: membership monotonicity,
  interface weakening (subtyping soundness), and inference soundness/principality
  (`self_member`). The proofs are re-checked every build via the stdlib preload; these
  tests pin the load-bearing consequences — a safe interface widens, and weakening
  cannot fabricate membership of a tag absent from the wider interface.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Tag = TA | TB | TC
    type TagList = TNil | TCons(Tag, TagList)
    type Handles indices (t: Tag, iface: TagList)
      HHere  : Handles(t, TCons(t, rest))
      HThere : Handles(t, rest) -> Handles(t, TCons(y, rest))
    type AllHandled indices (s: TagList, iface: TagList)
      AHNil  : AllHandled(TNil, iface)
      AHCons : Handles(t, iface) -> AllHandled(rest, iface) -> AllHandled(TCons(t, rest), iface)
    fn handles_mono({t: Tag}, {a: TagList}, {b: TagList}, h: Handles(t, a), sub: AllHandled(a, b)) -> Handles(t, b) = match h
      HHere() -> match sub
        AHCons(ht, srest) -> ht
      HThere(h2) -> match sub
        AHCons(sh, srest) -> handles_mono(h2, srest)
    fn weaken({s: TagList}, {a: TagList}, {b: TagList}, ah: AllHandled(s, a), sub: AllHandled(a, b)) -> AllHandled(s, b) = match ah
      AHNil() -> AHNil()
      AHCons(ht, ahrest) -> AHCons(handles_mono(ht, sub), weaken(ahrest, sub))
    fn weaken_cons({s: TagList}, {iface: TagList}, ah: AllHandled(s, iface), y: Tag) -> AllHandled(s, TCons(y, iface)) = match ah
      AHNil() -> AHNil()
      AHCons(ht, ahrest) -> AHCons(HThere(ht), weaken_cons(ahrest, y))
    fn self_member(s: TagList) -> AllHandled(s, s) = match s
      TNil() -> AHNil()
      TCons(t, rest) -> AHCons(HHere(), weaken_cons(self_member(rest), t))
  """

  defp verdict(defs) do
    case Program.elaborate("mod LawT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a safe interface can be widened (weaken), and the message set is its own interface" do
    defs = """
      fn widen(ah: AllHandled(TCons(TA, TNil), TCons(TA, TNil)), sub: AllHandled(TCons(TA, TNil), TCons(TA, TCons(TB, TNil)))) -> AllHandled(TCons(TA, TNil), TCons(TA, TCons(TB, TNil))) =
        weaken(ah, sub)
      fn own(s: TagList) -> AllHandled(s, s) = self_member(s)
    """

    assert verdict(defs) == :accept
  end

  test "membership is monotone: a proof in a subset transports to the superset" do
    defs = """
      fn mono(h: Handles(TA, TCons(TA, TNil)), sub: AllHandled(TCons(TA, TNil), TCons(TB, TCons(TA, TNil)))) -> Handles(TA, TCons(TB, TCons(TA, TNil))) =
        handles_mono(h, sub)
    """

    assert verdict(defs) == :accept
  end

  test "weaken cannot fabricate membership of a tag absent from the wider interface" do
    # self_member([TC]) : [TC] ⊆ [TC]; weakening to the EMPTY interface needs [TC] ⊆ [],
    # which is unprovable (AHNil is the wrong shape), so this is unconstructible.
    defs = """
      fn bad() -> AllHandled(TCons(TC, TNil), TNil) =
        weaken(self_member(TCons(TC, TNil)), AHNil())
    """

    assert verdict(defs) == :reject
  end
end
