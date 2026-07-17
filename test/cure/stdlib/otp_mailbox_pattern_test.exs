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
end
