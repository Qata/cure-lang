defmodule Cure.Stdlib.OtpSessionSubtypingTest do
  @moduledoc """
  `Std.Otp.SessionSubtyping` — Gay–Hole session subtyping. Internal choice (SSelect, ⊕) is
  covariant in its label set (offer fewer), external choice (SBranch, &) is contravariant (offer
  more). `sub_refl`/`sub_trans` make Sub a preorder; `sub_dual_antitone` shows duality reverses it.
  Cross-checked against Idris (oracle `session_subtyping`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.SessionSubtyping")
  end

  test "internal choice offering fewer labels is a subtype of one offering more" do
    # SSelect offering only LA ({T,F,F}) is a subtype of SSelect offering LA and LB ({T,T,F}):
    # the smaller label set embeds into the larger (LSub via BLe pointwise).
    src = """
    mod SubSel
      use Std.Otp.SessionSubtyping
      fn ex() -> Sub(SSelect(MkLSet(T(), F(), F()), SEnd()), SSelect(MkLSet(T(), T(), F()), SEnd())) =
        SubSel(MkLSub(BLeT(), BLeF(), BLeF()), SubEnd())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "external choice is contravariant: offering more labels is a subtype of offering fewer" do
    src = """
    mod SubBra
      use Std.Otp.SessionSubtyping
      fn ex() -> Sub(SBranch(MkLSet(T(), T(), F()), SEnd()), SBranch(MkLSet(T(), F(), F()), SEnd())) =
        SubBra(MkLSub(BLeT(), BLeF(), BLeF()), SubEnd())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "subtyping is a preorder and duality is antitone" do
    src = """
    mod SubProps
      use Std.Otp.SessionSubtyping
      fn r() -> Sub(SSend(TA(), SEnd()), SSend(TA(), SEnd())) = sub_refl(SSend(TA(), SEnd()))
      fn anti({s: SType}, {t: SType}, p: Sub(s, t)) -> Sub(dual(t), dual(s)) = sub_dual_antitone(p)
      fn tr({a: SType}, {b: SType}, {c: SType}, p: Sub(a, b), q: Sub(b, c)) -> Sub(a, c) = sub_trans(p, q)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "narrowing: a subtype is safely substitutable in a compatible session" do
    # A selector offering only LA is a subtype of one offering LA|LB; if the latter is compatible
    # with a brancher offering LA|LB, narrow gives compatibility of the smaller selector with it.
    src = """
    mod SubNarrow
      use Std.Otp.SessionSubtyping
      fn sub() -> Sub(SSelect(MkLSet(T(), F(), F()), SEnd()), SSelect(MkLSet(T(), T(), F()), SEnd())) =
        SubSel(MkLSub(BLeT(), BLeF(), BLeF()), SubEnd())
      fn c0() -> Compat(SSelect(MkLSet(T(), T(), F()), SEnd()), SBranch(MkLSet(T(), T(), F()), SEnd())) =
        CSelBra(MkLSub(BLeT(), BLeT(), BLeF()), CEnd())
      fn narrowed() -> Compat(SSelect(MkLSet(T(), F(), F()), SEnd()), SBranch(MkLSet(T(), T(), F()), SEnd())) =
        narrow(sub(), c0())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
