defmodule Cure.Stdlib.OtpCallResultTest do
  @moduledoc """
  `Std.Otp.CallResult` — a gen_server:call result whose success payload has the request-determined
  value type `RepVal(reply_for(req))` (large elimination), or a clean failure. The dependent reply
  value type computes per request, and a consumer that ignores failure is rejected as non-total.
  Cross-checked against Idris (oracle `call_result`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.CallResult")
  end

  test "the success payload type is computed from the request (Nat for RGet, Bit for RPut)" do
    # Ok(RGet, S(Z)) type-checks only because RepVal(reply_for(RGet)) = Nat; Ok(RPut, B1) only
    # because RepVal(reply_for(RPut)) = Bit. A Bit where a Nat is required must be rejected.
    good = """
    mod CrGood
      use Std.Otp.CallResult
      fn a() -> CallResult(RGet()) = Ok(RGet(), S(Z()))
      fn b() -> CallResult(RPut()) = Ok(RPut(), B0())
    end
    """

    assert {:ok, _} = Program.elaborate(good)

    bad = """
    mod CrBad
      use Std.Otp.CallResult
      fn a() -> CallResult(RGet()) = Ok(RGet(), B1())
    end
    """

    assert {:error, _} = Program.elaborate(bad)
  end

  test "a consumer that ignores failure is rejected as non-total" do
    src = """
    mod CrPartial
      use Std.Otp.CallResult
      fn only_ok({r: Req}, res: CallResult(r)) -> Status = match res
        Ok(rr, v) -> Success()
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
