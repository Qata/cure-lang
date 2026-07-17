defmodule Cure.Stdlib.OtpKeyOrderTest do
  @moduledoc """
  `Std.Otp.KeyOrder` — the decidable total order on keys that every ordered OTP structure
  (gb_trees/gb_sets/ordsets, `Std.Otp.Bst`/`Std.Otp.Gbt`) steers by. Certifies the four total-order
  axioms — reflexivity, totality, antisymmetry, transitivity — so downstream search-tree and sorted
  invariants rest on a proven order, not an assumed one. Cross-checked against Idris (oracle `key_order`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.KeyOrder")
  end

  test "le is a decidable total order (reflexive, total, antisymmetric, transitive)" do
    src = """
    mod OrdLaw
      use Std.Otp.KeyOrder
      fn refl(a: OKey) -> Equivalent(OBit, le(a, a), OT()) =
        le_refl(a)
      fn total(a: OKey, b: OKey) -> Equivalent(OBit, orb(le(a, b), le(b, a)), OT()) =
        le_total(a, b)
      fn antisym(a: OKey, b: OKey, p: Equivalent(OBit, le(a, b), OT()), q: Equivalent(OBit, le(b, a), OT())) -> Equivalent(OKey, a, b) =
        le_antisym(a, b, p, q)
      fn trans(a: OKey, b: OKey, c: OKey, p: Equivalent(OBit, le(a, b), OT()), q: Equivalent(OBit, le(b, c), OT())) -> Equivalent(OBit, le(a, c), OT()) =
        le_trans(a, b, c, p, q)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
