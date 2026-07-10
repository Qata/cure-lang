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
  # When the elaborator threads the inner component's metavar through a depth->=3
  # unit-terminated Σ-telescope, delete the `@tag :skip` and this must pass.
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
