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

  test "star_unfold/star_fold: the Kleene star fixpoint law round-trips" do
    src = """
    mod StarInst
      use Std.Otp.MailboxPattern
      fn empty_star() -> Accepts(PStar(PAtom(TA)), MkMS(Z, Z, Z)) = AStar0()
      fn plus_form() -> Accepts(PPlus(POne, PTimes(PAtom(TA), PStar(PAtom(TA)))), MkMS(S(Z), Z, Z)) =
        APlusR(ATimes(MkMS(S(Z), Z, Z), MkMS(Z, Z, Z), AAtomA(), empty_star()))
      fn one_ta_star() -> Accepts(PStar(PAtom(TA)), MkMS(S(Z), Z, Z)) = star_fold(plus_form())
      fn back() -> Accepts(PPlus(POne, PTimes(PAtom(TA), PStar(PAtom(TA)))), MkMS(S(Z), Z, Z)) =
        star_unfold(one_ta_star())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "dist_fwd: E.(F+G) distributes to (E.F)+(E.G)" do
    src = """
    mod DistInst
      use Std.Otp.MailboxPattern
      fn bc() -> Accepts(PPlus(PAtom(TB), PAtom(TC)), MkMS(Z, S(Z), Z)) = APlusL(AAtomB())
      fn src_acc() -> Accepts(PTimes(PAtom(TA), PPlus(PAtom(TB), PAtom(TC))), MkMS(S(Z), S(Z), Z)) =
        ATimes(MkMS(S(Z), Z, Z), MkMS(Z, S(Z), Z), AAtomA(), bc())
      fn dist() -> Accepts(PPlus(PTimes(PAtom(TA), PAtom(TB)), PTimes(PAtom(TA), PAtom(TC))), MkMS(S(Z), S(Z), Z)) =
        dist_fwd(src_acc())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "PZero is the additive unit (plus_zero round-trips)" do
    src = """
    mod SemiInst
      use Std.Otp.MailboxPattern
      fn a_acc() -> Accepts(PAtom(TA), MkMS(S(Z), Z, Z)) = AAtomA()
      fn with_zero() -> Accepts(PPlus(PAtom(TA), PZero), MkMS(S(Z), Z, Z)) = plus_zero_bwd(a_acc())
      fn back() -> Accepts(PAtom(TA), MkMS(S(Z), Z, Z)) = plus_zero_fwd(with_zero())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "incl_sound: subtyping transports acceptance (TA <= TA + TB)" do
    src = """
    mod SubInst
      use Std.Otp.MailboxPattern
      fn a_acc() -> Accepts(PAtom(TA), MkMS(S(Z), Z, Z)) = AAtomA()
      fn widened() -> Accepts(PPlus(PAtom(TA), PAtom(TB)), MkMS(S(Z), Z, Z)) =
        incl_sound(IInL(IRefl()), a_acc())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "deriv_mono: subtyping is preserved by the derivative" do
    src = """
    mod DmInst
      use Std.Otp.MailboxPattern
      fn sub() -> Incl(PAtom(TA), PPlus(PAtom(TA), PAtom(TB))) = IInL(IRefl())
      fn dmono() -> Incl(deriv(PAtom(TA), TA), deriv(PPlus(PAtom(TA), PAtom(TB)), TA)) =
        deriv_mono(TA, sub())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
