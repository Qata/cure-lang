defmodule Cure.Stdlib.OtpSetTest do
  @moduledoc """
  `Std.Otp.Set` — the BEAM `:sets`/`:ordsets` library. `union_member` proves the defining law of
  set union: membership distributes over union as boolean OR — an element is in the union exactly
  when it is in one of the parts. Cross-checked against Idris (oracle `set`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Set")
  end

  test "membership distributes over union as boolean OR" do
    src = """
    mod SetLaw
      use Std.Otp.Set
      fn law(x: Key, s1: Set, s2: Set) -> Equivalent(B, mem(x, union(s1, s2)), orb(mem(x, s1), mem(x, s2))) =
        union_member(x, s1, s2)
      fn inst() -> Equivalent(B, mem(KB(), union(SetCons(KA(), SetNil()), SetCons(KB(), SetNil()))), orb(mem(KB(), SetCons(KA(), SetNil())), mem(KB(), SetCons(KB(), SetNil())))) =
        union_member(KB(), SetCons(KA(), SetNil()), SetCons(KB(), SetNil()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
