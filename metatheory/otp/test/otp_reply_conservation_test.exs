defmodule Cure.Stdlib.OtpReplyConservationTest do
  @moduledoc """
  `Std.Otp.ReplyConservation` — the LINEAR reply capability's *consumed-exactly-once*
  as an OPERATIONAL conservation law (the operational dual of `Std.Otp.Proof`'s
  intrinsic QTT discipline): answering an outstanding capability conserves the total
  (pending capabilities + replies), a complete run answers exactly as many replies as
  it began with capabilities (`drain`), and no reply can be produced without consuming
  a capability. The proof is re-checked every build via the stdlib preload; these
  tests pin the safety content — the no-capability-no-reply guard, and that a step
  from a zero-pending configuration is unconstructible.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # Self-contained calculus (mirrors metatheory/otp/src/otp_reply_conservation.cure). Uses the
  # cross-module Std.Nat/Std.Proof lemmas — exercising the prelude-in-slice fix.
  @calculus """
    use Std.Nat
    use Std.Proof
    fn trans({t: Type}, {x: t}, {y: t}, {z: t}, e1: Equivalent(t, x, y), e2: Equivalent(t, y, z)) -> Equivalent(t, x, z) =
      rewrite e1 in e2
    type Config = MkConfig(Nat, Nat)
    type LStep indices (before: Config, after: Config)
      LAnswer : (p: Nat) -> (a: Nat) -> LStep(MkConfig(S(p), a), MkConfig(p, S(a)))
    fn total(c: Config) -> Nat = match c
      MkConfig(p, a) -> plus(p, a)
    fn step_conserves(p: Nat, a: Nat, s: LStep(MkConfig(S(p), a), MkConfig(p, S(a)))) -> Equivalent(Nat, total(MkConfig(S(p), a)), total(MkConfig(p, S(a)))) =
      rewrite plus_succ_right(p, a) in reflexive(S(plus(p, a)))
    type LStar indices (before: Config, after: Config)
      LDone : LStar(c, c)
      LThen : LStep(x, y) -> LStar(y, z) -> LStar(x, z)
    fn total_invariant({b: Config}, {a2: Config}, r: LStar(b, a2)) -> Equivalent(Nat, total(b), total(a2)) = match r
      LDone() -> reflexive(total(b))
      LThen(st, rest) -> match st
        LAnswer(p, a) -> trans(step_conserves(p, a, st), total_invariant(rest))
    fn drain(n: Nat, m: Nat, r: LStar(MkConfig(n, Z), MkConfig(Z, m))) -> Equivalent(Nat, n, m) =
      rewrite plus_zero_right(n) in total_invariant(r)
  """

  defp verdict(defs) do
    case Program.elaborate("mod ReplyCons\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the conservation + drain proofs and a concrete step type-check" do
    defs = """
      fn a_step() -> LStep(MkConfig(S(Z), Z), MkConfig(Z, S(Z))) = LAnswer(Z, Z)
    """

    assert verdict(defs) == :accept
  end

  test "no reply without a capability: a step from zero-pending is absurd (uninhabited)" do
    defs = """
      type Void = |
      fn no_answer_without_cap({a: Nat}, {after: Config}, s: LStep(MkConfig(Z, a), after)) -> Void = match s
    """

    assert verdict(defs) == :accept
  end

  test "a step answering from a zero-pending config is unconstructible" do
    # LAnswer demands S(p) pending; MkConfig(Z, _) cannot supply it.
    defs = """
      fn bad_answer() -> LStep(MkConfig(Z, Z), MkConfig(Z, S(Z))) = LAnswer(Z, Z)
    """

    assert verdict(defs) == :reject
  end

  test "conservation cannot be claimed to CHANGE the total" do
    # total is invariant, so a step cannot witness total(before) = S(total(before)).
    defs = """
      fn bogus(p: Nat, a: Nat, s: LStep(MkConfig(S(p), a), MkConfig(p, S(a)))) -> Equivalent(Nat, total(MkConfig(S(p), a)), S(total(MkConfig(S(p), a)))) =
        rewrite plus_succ_right(p, a) in reflexive(S(plus(p, a)))
    """

    assert verdict(defs) == :reject
  end
end
