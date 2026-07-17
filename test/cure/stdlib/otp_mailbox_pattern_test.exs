defmodule Cure.Stdlib.OtpMailboxPatternTest do
  @moduledoc """
  `Std.Otp.MailboxPattern` — commutative-regex mailbox types (the multiplicity/counting model
  the tag-set inference cannot reach). Pins the acceptance relation over multisets (Parikh
  vectors) and the defining COMMUTATIVE laws: `times_comm` (concatenation of patterns commutes
  up to accepted multisets) and `plus_comm`/`msadd_comm`. Cross-checked against Idris (oracle
  `mailbox_pattern`); re-checked every build via the stdlib preload.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.MailboxPattern")
  end

  test "times_comm: {TA}.{TB} and {TB}.{TA} accept the same message bag" do
    # The bag {one TA, one TB} is denoted by PTimes(PAtom TA, PAtom TB); commutativity gives
    # that PTimes(PAtom TB, PAtom TA) denotes it too — a mailbox is an unordered bag.
    src = """
    mod MpInst
      use Std.Otp.MailboxPattern
      fn ab_acc() -> Accepts(PTimes(PAtom(TA), PAtom(TB)), MkMS(S(Z), S(Z), Z)) =
        ATimes(MkMS(S(Z), Z, Z), MkMS(Z, S(Z), Z), AAtomA(), AAtomB())
      fn ba_acc() -> Accepts(PTimes(PAtom(TB), PAtom(TA)), MkMS(S(Z), S(Z), Z)) =
        times_comm(ab_acc())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "one_times: the empty pattern is the unit of concatenation" do
    # 1 . {TA} accepts the bag {TA}, and one_times strips the unit to give {TA} directly.
    src = """
    mod MpUnit
      use Std.Otp.MailboxPattern
      fn one_ta() -> Accepts(PTimes(POne, PAtom(TA)), MkMS(S(Z), Z, Z)) =
        ATimes(MkMS(Z, Z, Z), MkMS(S(Z), Z, Z), AOne(), AAtomA())
      fn ta_from_one() -> Accepts(PAtom(TA), MkMS(S(Z), Z, Z)) =
        one_times(one_ta())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "nullable_sound: a nullable pattern accepts the empty bag" do
    # *{TA} (zero or more TA) is nullable — it accepts the empty mailbox — and nullable_sound
    # turns that decision into the acceptance derivation.
    src = """
    mod MpNull
      use Std.Otp.MailboxPattern
      fn star_nullable() -> Accepts(PStar(PAtom(TA)), MkMS(Z, Z, Z)) =
        nullable_sound(PStar(PAtom(TA)), reflexive(T))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "deriv_sound: if the derivative accepts the rest, the pattern accepts the whole bag" do
    # The derivative of {TA}.{TB} by TA accepts the bag {TB}; soundness rebuilds acceptance of
    # {TA,TB} by the original pattern (the peeled TA relocated back in).
    src = """
    mod DsInst
      use Std.Otp.MailboxPattern
      fn d_acc() -> Accepts(deriv(PTimes(PAtom(TA), PAtom(TB)), TA), MkMS(Z, S(Z), Z)) =
        APlusL(ATimes(MkMS(Z, Z, Z), MkMS(Z, S(Z), Z), AOne(), AAtomB()))
      fn full() -> Accepts(PTimes(PAtom(TA), PAtom(TB)), msadd(MkMS(Z, S(Z), Z), singleton(TA))) =
        deriv_sound(PTimes(PAtom(TA), PAtom(TB)), TA, MkMS(Z, S(Z), Z), d_acc())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
