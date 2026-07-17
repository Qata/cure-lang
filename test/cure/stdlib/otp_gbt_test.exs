defmodule Cure.Stdlib.OtpGbtTest do
  @moduledoc """
  `Std.Otp.Gbt` — Erlang gb_trees as an ordered key→value map (`enter`/`lookup`). The two defining
  finite-map laws: `lookup_insert_eq` (looking up a key you just entered returns the entered value)
  and `lookup_insert_neq` (entering a different key leaves an unrelated lookup unchanged). Keys are
  a finite ordered domain so `gcmp` reduces at proof time. Cross-checked against Idris (oracle `gbt`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Gbt")
  end

  test "gb_trees map: lookup after enter returns the entered value, other keys unchanged" do
    src = """
    mod GbtLaw
      use Std.Otp.Gbt
      fn got(k: GKey, val: Nat, t: GTree) -> Equivalent(GOpt, lookup(k, insert(k, val, t)), GSome(val)) =
        lookup_insert_eq(k, val, t)
      fn other(x: GKey, k: GKey, val: Nat, t: GTree, neq: Equivalent(GBit, gkeq(x, k), BF())) -> Equivalent(GOpt, lookup(x, insert(k, val, t)), lookup(x, t)) =
        lookup_insert_neq(x, k, val, t, neq)
      fn inst() -> Equivalent(GOpt, lookup(GB(), insert(GB(), S(S(Z())), GNode(GLeaf(), GA(), Z(), GLeaf()))), GSome(S(S(Z())))) =
        lookup_insert_eq(GB(), S(S(Z())), GNode(GLeaf(), GA(), Z(), GLeaf()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
