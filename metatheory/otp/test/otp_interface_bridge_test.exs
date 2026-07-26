defmodule Cure.Stdlib.OtpInterfaceBridgeTest do
  @moduledoc """
  `Std.Otp.InterfaceBridge` — the correspondence between the finite `IF` lattice (where the
  Kleene stabilization argument of `Std.Otp.FiniteFixpoint` lives) and the `TagList`
  membership order the adequacy proof consumes. Pins the two directions:
  `denote_complete` (a set bit is a member of `denote(x)`) and `sub_allhandled` (the finite
  order `Sub` embeds into `AllHandled(denote(x), denote(y))`), so `map_lfp_le`'s `Sub`
  conclusion transfers to a membership fixed point. Cross-checked against Idris (oracle
  `interface_bridge`); re-checked every build via the stdlib preload.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.InterfaceBridge")
  end

  test "sub_allhandled embeds a concrete Sub into TagList membership" do
    # Sub(MkIF(F,T,F), MkIF(T,T,F)): the source sets only tag B, the target sets A and B, so
    # denote(source) = [TB] is contained in denote(target) = [TA, TB]. A non-vacuous use of
    # the order embedding via `use`.
    src = """
    mod BrInst
      use Std.Otp.FiniteFixpoint
      use Std.Otp.InterfaceBridge
      fn ex() -> AllHandled(denote(MkIF(F, T, F)), denote(MkIF(T, T, F))) =
        sub_allhandled(MkIF(F, T, F), MkIF(T, T, F), MkSub(ImpFT(), ImpTT(), ImpFF()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
