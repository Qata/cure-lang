defmodule Cure.Stdlib.OtpBagTest do
  @moduledoc """
  `Std.Otp.Bag` — ETS bag/duplicate_bag multiset semantics. Unlike a set table (overwrite) or an
  ordered map, a duplicate_bag keeps every insertion, so the meaningful observation is a key's
  multiplicity `count(k, t)`. `insert_incr` (insert adds one occurrence), `insert_other` (a
  different key's count is untouched), `delete_insert` (delete_one undoes an insert). Cross-checked
  against Idris (oracle `bag`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Bag")
  end

  test "multiset count algebra: insert increments, other keys untouched, delete_one undoes insert" do
    src = """
    mod BagLaw
      use Std.Otp.Bag
      fn incr(k: MKey, t: Bag) -> Equivalent(Nat, count(k, insert(k, t)), S(count(k, t))) =
        insert_incr(k, t)
      fn other(x: MKey, k: MKey, t: Bag, neq: Equivalent(MBit, keq(x, k), MF())) -> Equivalent(Nat, count(x, insert(k, t)), count(x, t)) =
        insert_other(x, k, t, neq)
      fn undo(k: MKey, t: Bag) -> Equivalent(Bag, delete_one(k, insert(k, t)), t) =
        delete_insert(k, t)
      fn twice() -> Equivalent(Nat, count(MA(), insert(MA(), insert(MA(), BNil()))), S(S(Z()))) =
        insert_incr(MA(), insert(MA(), BNil()))
      fn decr(k: MKey, t: Bag) -> Equivalent(Nat, count(k, delete_one(k, t)), mpred(count(k, t))) =
        count_delete_one(k, t)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
