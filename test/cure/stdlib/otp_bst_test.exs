defmodule Cure.Stdlib.OtpBstTest do
  @moduledoc """
  `Std.Otp.Bst` — the ordered binary search tree behind Erlang gb_trees/gb_sets. `insert_member`
  proves the defining search-tree law: after inserting a key, a subsequent search for it succeeds
  (`member(k, insert(k, t)) = T`), because `member` and `insert` steer by the same comparison at
  every node. Keys are a finite ordered domain so `kcmp` reduces at proof time. Cross-checked
  against Idris (oracle `bst`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Bst")
  end

  test "a search-tree insert makes the key findable" do
    src = """
    mod BstLaw
      use Std.Otp.Bst
      fn law(k: Key, t: Tree) -> Equivalent(B, member(k, insert(k, t)), T()) =
        insert_member(k, t)
      fn empty(k: Key) -> Equivalent(B, member(k, Leaf()), F()) =
        member_leaf(k)
      fn inst() -> Equivalent(B, member(KB(), insert(KB(), Node(Leaf(), KA(), Node(Leaf(), KC(), Leaf())))), T()) =
        insert_member(KB(), Node(Leaf(), KA(), Node(Leaf(), KC(), Leaf())))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
