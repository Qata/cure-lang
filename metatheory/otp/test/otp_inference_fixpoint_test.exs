defmodule Cure.Stdlib.OtpInferenceFixpointTest do
  @moduledoc """
  `Std.Otp.InferenceFixpoint` — the pre-fixpoint bound (`lfp_le`), the principality direction
  of Knaster-Tarski for mailbox-inference over recursive behaviours: with `f` monotone and `a`
  a pre-fixed point (`f(a) ⊆ a`), every Kleene iterate `f^n(⊥) ⊆ a`. Proved end to end (no
  finite-height stabilization needed), re-checked on preload.

  Red-green on the proof term: the correct induction (bottom trivially bounded; the step
  composes monotonicity with the pre-fixpoint by transitivity) is accepted, and two broken
  proofs — a bottom-shaped step and a mono/pre swap that transposes the bound — are refused.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # The fixpoint calculus WITHOUT `lfp_le` — the proof under test is supplied per-case.
  @calculus """
    type Tag = TA | TB | TC
    type TagList = TNil | TCons(Tag, TagList)
    type Handles indices (t: Tag, iface: TagList)
      HHere  : Handles(t, TCons(t, rest))
      HThere : Handles(t, rest) -> Handles(t, TCons(y, rest))
    type AllHandled indices (s: TagList, iface: TagList)
      AHNil  : AllHandled(TNil, iface)
      AHCons : Handles(t, iface) -> AllHandled(rest, iface) -> AllHandled(TCons(t, rest), iface)
    type Nat = Z | S(Nat)
    fn iterate(f: (TagList) -> TagList, x: TagList, n: Nat) -> TagList = match n
      Z()  -> x
      S(k) -> f(iterate(f, x, k))
    fn handles_weaken({t: Tag}, {y: TagList}, {z: TagList}, h: Handles(t, y), sub: AllHandled(y, z)) -> Handles(t, z) = match h
      HHere()    -> match sub
        AHCons(ht, srest) -> ht
      HThere(h2) -> match sub
        AHCons(hh, srest) -> handles_weaken(h2, srest)
    fn all_handled_trans({x: TagList}, {y: TagList}, {z: TagList}, xy: AllHandled(x, y), yz: AllHandled(y, z)) -> AllHandled(x, z) = match xy
      AHNil()            -> AHNil()
      AHCons(hx, xrest)  -> AHCons(handles_weaken(hx, yz), all_handled_trans(xrest, yz))
  """

  defp verdict(defs) do
    case Program.elaborate("mod FpT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  @sig "fn lfp_le(f: (TagList) -> TagList, mono: (x: TagList) -> (y: TagList) -> (AllHandled(x, y)) -> AllHandled(f(x), f(y)), a: TagList, pre: AllHandled(f(a), a), n: Nat) -> AllHandled(iterate(f, TNil, n), a) = match n"

  test "the pre-fixpoint bound type-checks (the theorem holds)" do
    defs = """
      #{@sig}
        Z()  -> AHNil()
        S(k) -> all_handled_trans(mono(iterate(f, TNil, k), a, lfp_le(f, mono, a, pre, k)), pre)
    """

    assert verdict(defs) == :accept
  end

  test "a bottom-shaped step is refused (S(k) must bound f(iterate_k), not TNil)" do
    defs = """
      #{@sig}
        Z()  -> AHNil()
        S(k) -> AHNil()
    """

    assert verdict(defs) == :reject
  end

  test "transposing the transitivity composition is refused (bound goes the wrong way)" do
    # Swapping the two AllHandled arguments to all_handled_trans claims f(iterate_k) ⊆ a via
    # (f(a) ⊆ a) then (f(iterate_k) ⊆ f(a)), which is not composable in that order.
    defs = """
      #{@sig}
        Z()  -> AHNil()
        S(k) -> all_handled_trans(pre, mono(iterate(f, TNil, k), a, lfp_le(f, mono, a, pre, k)))
    """

    assert verdict(defs) == :reject
  end
end
