defmodule Cure.Stdlib.OtpTreeTest do
  @moduledoc """
  `Std.Otp.Tree` — the binary tree backing Erlang gb_trees/gb_sets. `mirror_involution` proves
  reflecting a tree twice is the identity; `size_mirror` proves mirroring preserves the node count
  (via add_comm, since mirror swaps subtrees). Cross-checked against Idris (oracle `tree`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Tree")
  end

  test "mirror is an involution and preserves size" do
    src = """
    mod TrLaws
      use Std.Otp.Tree
      fn invol(t: Tree) -> Equivalent(Tree, mirror(mirror(t)), t) = mirror_involution(t)
      fn keeps_size(t: Tree) -> Equivalent(Nat, size(mirror(t)), size(t)) = size_mirror(t)
      fn inst() -> Equivalent(Tree, mirror(mirror(Node(Leaf(), Z(), Node(Leaf(), S(Z()), Leaf())))), Node(Leaf(), Z(), Node(Leaf(), S(Z()), Leaf()))) =
        mirror_involution(Node(Leaf(), Z(), Node(Leaf(), S(Z()), Leaf())))
      fn traversal(t: Tree) -> Equivalent(TList, flatten(mirror(t)), lrev(flatten(t))) = flatten_mirror(t)
      fn size_eq_len(t: Tree) -> Equivalent(Nat, llen(flatten(t)), size(t)) = size_flatten(t)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
