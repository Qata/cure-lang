defmodule Cure.Elab.FoldAccumulatorPolySeedReachTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @moduletag :reach

  # REACH PIN (#23 value-surface parity) — a general elaborator inference gap,
  # NOT a soundness issue. Surfaced while parameterising `Std.Map` to `Map(k, v)`
  # so `Std.Set` could elaborate: `Std.Set.from_list`/`intersection`/`difference`
  # all seed a `foldl` with a polymorphic empty map, `foldl(list, new(), lambda)`.
  #
  # Symptom: a polymorphic function used as the ACCUMULATOR argument of a
  # higher-order fold, whose type parameters are determined only transitively by
  # the fold's lambda (through the accumulator type `b`), has its metavariables
  # committed BEFORE the lambda constrains `b` — leaving them unsolved:
  # `{:error, {:unsolved_metavariables, :new}}`.
  #
  # Boundary (see scratchpad/nullary.exs + foldacc.exs):
  #   * `fn empty() -> Map(t, Bool) = new()`            -> OK   (return-type flow
  #                                                              pins the seed)
  #   * `fn single(x: t) -> Map(t,Bool) = put(x,true,new())` -> OK (arg pins it)
  #   * `foldl(list, new(), lambda)` seed pinned by lambda  -> FAIL (this pin)
  # So the trigger is a polymorphic seed in accumulator position whose params are
  # constrained only by a later function-typed argument.
  #
  # This blocks the dependent side of `Std.Set` (the other blocker is that the
  # classic checker cannot instantiate the parameterised `Map(k,v)` at all — see
  # [[dep-pipeline-survey-2026-07-11]]). When the elaborator propagates the
  # fold's lambda-derived accumulator type back into the seed argument, delete the
  # `@tag :skip` and this must pass.
  @tag :skip
  test "polymorphic seed in foldl accumulator position is solved from the lambda" do
    src = """
    mod Probe
      opaque type Map(k, v)
      @extern(:maps, :new, 0)
      fn new() -> Map(k, v)
      @extern(:maps, :put, 3)
      fn put(key: k, value: v, map: Map(k, v)) -> Map(k, v)
      @extern(:lists, :foldl, 3)
      fn foldl(list: List(a), acc: b, f: a -> b -> b) -> b
      fn from_list(list: List(t)) -> Map(t, Bool) =
        foldl(list, new(), fn(elem) -> fn(acc) -> put(elem, true, acc))
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
