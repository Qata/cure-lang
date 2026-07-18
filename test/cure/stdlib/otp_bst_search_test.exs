defmodule Cure.Stdlib.OtpBstSearchTest do
  @moduledoc """
  `Std.Otp.BstSearch` — SEARCH-TREE SEARCH SOUNDNESS. On a well-formed binary search tree
  (`is_bst(t) = OT`), binary search agrees with linear scan: `mem_eq_lmem` proves
  `mem(x, t) = lmem(x, t)` — steering by the key comparison never misses an element a full scan
  would find. This is the extrinsic-invariant formalization (boolean `is_bst`/`alllt`/`allgt`),
  the machinery certified `delete` builds on. The proof rests on the strict order (`strict_trans`)
  via the "below/above bound ⟹ not linearly present" lemmas. Cross-checked against Idris (oracle
  `bst_search`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.BstSearch")
  end

  test "on a well-formed BST, binary search agrees with linear scan" do
    src = """
    mod BstSearchLaw
      use Std.Otp.BstSearch
      fn sound(x: OKey, t: Tree, bst: Equivalent(OBit, isbst(t), OT())) -> Equivalent(OBit, mem(x, t), lmem(x, t)) =
        mem_eq_lmem(x, t, bst)
      fn below(x: OKey, b: OKey, t: Tree, pxb: Equivalent(OBit, cmp(x, b), OT()), pgt: Equivalent(OBit, allgt(t, b), OT())) -> Equivalent(OBit, lmem(x, t), OF()) =
        below_not_lmem(x, b, t, pxb, pgt)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
