defmodule Cure.Stdlib.OtpEffAlgebraTest do
  @moduledoc """
  `Std.Otp.EffAlgebra` — OTP effect programs form a MONOID under sequential composition. Since
  the message operations carry no result, an effectful program is a sequence of commands and
  `seq` is append; `seq_nil_l`/`seq_nil_r`/`seq_assoc` certify `(Eff, seq, ENil)` is a monoid,
  so effect programs can be reassociated and unit-simplified. Cross-checked against Idris
  (oracle `eff_algebra`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.EffAlgebra")
  end

  test "seq_nil_r: ENil is a right unit of effect sequencing" do
    src = """
    mod EaInst
      use Std.Otp.EffAlgebra
      fn ex() -> Equivalent(Eff, seq(ECons(OSpawn, ENil()), ENil()), ECons(OSpawn, ENil())) =
        seq_nil_r(ECons(OSpawn, ENil()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
