defmodule Cure.Elab.TupleTelescopeListMatchReachTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @moduletag :reach

  # REACH PIN (#23 value-surface parity) — a known elaborator-completeness gap,
  # NOT a soundness issue. Std.Match's `first_two` works around this by returning
  # a nested/`Option`-wrapped tuple; this test pins the underlying gap so it is
  # repaired rather than left dodged (cure-porting: "a workaround is not a
  # repair").
  #
  # Symptom: a Σ-telescope tuple RETURN type of arity >= 3 that contains a
  # `List(_)` component fails to elaborate when the function body produces it
  # from a `match` on a `List` scrutinee — the inner List's `Nil` constructor
  # element metavar is left unsolved: `{:error, {:unsolved_metavariables, :Nil}}`.
  #
  # Boundary established by probing (see scratchpad/reachpin.exs):
  #   * arity-2 tuple with a List tail  -> OK   (pair threads the metavar fine)
  #   * arity-3 tuple of scalars only   -> OK   (no inner List, no gap)
  #   * arity-3 tuple WITH a List comp. -> FAIL (this pin)
  # So the trigger is the combination: telescope depth >= 3 AND an inner
  # inductive (List) component whose element type must flow from the scrutinee.
  #
  # LOCALIZED (2026-07-11): the bug is in `elaborate_match`
  # (elaborator.ex:1922), NOT the tuple builder. Evidence: the SAME triple-with-
  # List tuple built WITHOUT a match — `fn f(d: a) -> Tuple(a, a, List(a)) =
  # %[d, d, []]` (probe V2) — elaborates fine, so `check_tuple_against/5`
  # (elaborator.ex:1485) handles depth->=3 + inner List correctly. Only the `match`
  # wrapper fails. List's `a` is a PARAMETER (not an index), so `build_motive`
  # produces a CONSTANT motive = `result_type_term` (`Tuple(a,a,List(a))`); yet the
  # Nil branch's List element metavar is left unsolved (`:Nil`) only when that
  # constant result telescope is depth->=3 with an inner List (depth-2 `Tuple(a,
  # List(a))` = probe R3 works; depth-3 all-scalar = R4 works). So the remaining
  # dig is: why the constant-motive branch checking at result-telescope depth->=3
  # fails to tie the Nil ctor's element param to the scrutinee's `a`. Start at
  # `build_motive` + `elaborate_branches`/`elaborate_matched_branch` (the const-
  # motive path over a parameter-only family), NOT `check_tuple_against`.
  @tag :skip
  test "3-ary tuple with a List component built from a List-scrutinee match elaborates" do
    src = """
    mod Probe
      fn f(list: List(a), d: a) -> Tuple(a, a, List(a)) =
        match list
          [h | t] -> %[h, d, t]
          []      -> %[d, d, []]
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
