defmodule Cure.Stdlib.OtpEtsTest do
  @moduledoc """
  `Std.Otp.Ets` — a typed ETS (set-semantics) key/value table. `lookup_insert_eq` proves
  lookup-after-insert returns the inserted value; `lookup_insert_neq` proves a write to a different
  key doesn't disturb a lookup (impossible same-key case refuted via an Empty discriminator).
  Cross-checked against Idris (oracle `ets`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Ets")
  end

  test "lookup-after-insert returns the inserted value" do
    src = """
    mod EtsGet
      use Std.Otp.Ets
      fn law(k: Key, v: Nat, t: Table) -> Equivalent(Opt, lookup(k, insert(k, v, t)), OSome(v)) =
        lookup_insert_eq(k, v, t)
      fn inst() -> Equivalent(Opt, lookup(KB(), insert(KB(), S(Z()), TEmpty())), OSome(S(Z()))) =
        lookup_insert_eq(KB(), S(Z()), TEmpty())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "insert at a different key leaves a lookup unchanged" do
    src = """
    mod EtsNeq
      use Std.Otp.Ets
      fn law(k: Key, k2: Key, v: Nat, t: Table, neq: Equivalent(B, key_eq(k, k2), F())) -> Equivalent(Opt, lookup(k, insert(k2, v, t)), lookup(k, t)) =
        lookup_insert_neq(k, k2, v, t, neq)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
