defmodule Cure.Stdlib.OtpSessionTest do
  @moduledoc """
  `Std.Otp.Session` — binary session types + duality. `dual_involution` proves dualizing twice
  returns the original; `compat_dual` proves compatible endpoints are exactly dual endpoints
  (communication safety = duality). Cross-checked against Idris (oracle `session`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Session")
  end

  test "compatible endpoints are dual, and duality is an involution" do
    # !TA.?TB.end is compatible with ?TA.!TB.end, and compat_dual shows the first is the dual of
    # the second; dual_involution shows dualizing twice is the identity.
    src = """
    mod SsInst
      use Std.Otp.Session
      fn compat() -> Compat(SSend(TA, SRecv(TB, SEnd())), SRecv(TA, SSend(TB, SEnd()))) =
        CSR(TA, CRS(TB, CEnd()))
      fn is_dual() -> Equivalent(SType, SSend(TA, SRecv(TB, SEnd())), dual(SRecv(TA, SSend(TB, SEnd())))) =
        compat_dual(compat())
      fn invol() -> Equivalent(SType, dual(dual(SSend(TA, SEnd()))), SSend(TA, SEnd())) =
        dual_involution(SSend(TA, SEnd()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "session_preservation: a compatible session stays compatible after a communication step" do
    # !TA.end vs ?TA.end are compatible; after the TA exchange both are end, still compatible.
    src = """
    mod SpInst
      use Std.Otp.Session
      fn c0() -> Compat(SSend(TA, SEnd()), SRecv(TA, SEnd())) = CSR(TA, CEnd())
      fn step() -> SStep(SSend(TA, SEnd()), SRecv(TA, SEnd()), SEnd(), SEnd()) = StepSR()
      fn stepped() -> Compat(SEnd(), SEnd()) = session_preservation(c0(), step())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
