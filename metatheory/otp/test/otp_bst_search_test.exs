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
      fn del_preserves(k: OKey, t: Tree, bst: Equivalent(OBit, isbst(t), OT())) -> Equivalent(OBit, isbst(delete(k, t)), OT()) =
        delete_bst(k, t, bst)
      fn merge_preserves(l: Tree, r: Tree, m: OKey, bl: Equivalent(OBit, isbst(l), OT()), br: Equivalent(OBit, isbst(r), OT()), plt: Equivalent(OBit, alllt(l, m), OT()), pgt: Equivalent(OBit, allgt(r, m), OT())) -> Equivalent(OBit, isbst(merge(l, r)), OT()) =
        merge_bst(l, r, m, bl, br, plt, pgt)
      fn del_removes(k: OKey, t: Tree, bst: Equivalent(OBit, isbst(t), OT())) -> Equivalent(OBit, mem(k, delete(k, t)), OF()) =
        mem_delete_eq(k, t, bst)
      fn del_preserves_others(x: OKey, k: OKey, t: Tree, bst: Equivalent(OBit, isbst(t), OT()), neq: Equivalent(OBit, keq(x, k), OF())) -> Equivalent(OBit, mem(x, delete(k, t)), mem(x, t)) =
        mem_delete_neq(x, k, t, bst, neq)
      fn flatten_is_sorted(t: Tree, bst: Equivalent(OBit, isbst(t), OT())) -> Equivalent(OBit, sorted(flatten(t)), OT()) =
        flatten_sorted(t, bst)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
