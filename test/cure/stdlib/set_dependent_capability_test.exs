defmodule Cure.Stdlib.SetDependentCapabilityTest do
  @moduledoc """
  #18-readiness capability proof for `Std.Set` — the LAST stdlib module whose
  dependent-pipeline capability was in doubt.

  History: `Std.Set` delegates to `Std.Map` and, in its committed form, seeds
  three functions (`from_list`, `intersection`, `difference`) with a
  `Std.List.foldl(list, Std.Map.new(), lambda)`. Against a *parameterised*
  `Map(k, v)` that fold hits a real elaborator inference gap — the polymorphic
  accumulator seed's metavariables are committed before the fold's lambda
  constrains the accumulator type (see
  `test/cure/elab/fold_accumulator_poly_seed_reach_test.exs`). That gap was
  previously believed to require an operator-level architectural decision
  (meta-aware Values in the trusted kernel, or a parallel meta-checker).

  This test records the resolution: the fold is not necessary. Rewritten with
  ordinary **structural recursion** over the element list, every `Std.Set`
  operation — including `intersection`/`difference` — elaborates on the
  dependent pipeline against a parameterised `Map(k, v)`, using only bare `Bool`
  (no `use Std.Bool`). Each `match` branch is checked against the function's
  declared return type, so `[] -> new()` has its metavariables pinned by the
  expected type; there is no polymorphic accumulator seeded through a fold. No
  kernel (`lib/cure/core/*`) change, no elaborator change — a pure surface form.

  So `Std.Set` is dependent-CAPABLE. It is not in the live-file `@green` firewall
  (`dependent_elaboration_parity_test.exs`) only because it is
  CLASSIC-COEXISTENCE-blocked exactly like `show`/`io`/`access`: the classic
  checker (`lib/cure/types/*`) cannot instantiate a parameterised `Map(k, v)`
  across `from_list`'s match branches — `compile_string` on this same source
  fails `E033: match branches have no common upper bound: Map(k, v) vs
  Map(t, Bool)`. So the committed `lib/std/set.cure` must keep its
  classic-compatible bare-`Map` form until the classic pipeline is deleted (#18),
  at which point it is rewritten to the form proven here.

  The source below is `lib/std/set.cure`'s rip-out target form: the same eleven
  operations, `Map` parameterised as `Map(t, Bool)`, and the three fold-seeded
  functions rewritten with structural recursion. Keep it in lock-step with
  `lib/std/set.cure` when that file is migrated at rip-out.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @set_ripout_form """
  mod Std.SetDep
    opaque type Map(k, v)
    @extern(:maps, :new, 0)
    fn new() -> Map(k, v)
    @extern(:maps, :put, 3)
    fn put(key: k, value: v, map: Map(k, v)) -> Map(k, v)
    @extern(:maps, :remove, 2)
    fn mremove(key: k, map: Map(k, v)) -> Map(k, v)
    @extern(:maps, :is_key, 2)
    fn has_key(key: k, map: Map(k, v)) -> Bool
    @extern(:maps, :size, 1)
    fn msize(map: Map(k, v)) -> Int
    @extern(:maps, :keys, 1)
    fn keys(map: Map(k, v)) -> List(k)
    @extern(:maps, :merge, 2)
    fn mmerge(a: Map(k, v), b: Map(k, v)) -> Map(k, v)

    fn new_set() -> Map(t, Bool) = new()
    fn add(elem: t, set: Map(t, Bool)) -> Map(t, Bool) = put(elem, true, set)
    fn remove(elem: t, set: Map(t, Bool)) -> Map(t, Bool) = mremove(elem, set)
    fn member(elem: t, set: Map(t, Bool)) -> Bool = has_key(elem, set)
    fn size(set: Map(t, Bool)) -> Int = msize(set)
    fn is_empty(set: Map(t, Bool)) -> Bool = msize(set) == 0
    fn to_list(set: Map(t, Bool)) -> List(t) = keys(set)
    fn union(a: Map(t, Bool), b: Map(t, Bool)) -> Map(t, Bool) = mmerge(a, b)

    fn from_list(list: List(t)) -> Map(t, Bool) =
      match list
        [] -> new()
        [h | rest] -> add(h, from_list(rest))

    local fn intersect_go(elems: List(t), b: Map(t, Bool), acc: Map(t, Bool)) -> Map(t, Bool) =
      match elems
        [] -> acc
        [h | rest] ->
          pickup
            member(h, b) -> intersect_go(rest, b, add(h, acc))
            else         -> intersect_go(rest, b, acc)
    fn intersection(a: Map(t, Bool), b: Map(t, Bool)) -> Map(t, Bool) =
      intersect_go(to_list(a), b, new())

    local fn diff_go(elems: List(t), b: Map(t, Bool), acc: Map(t, Bool)) -> Map(t, Bool) =
      match elems
        [] -> acc
        [h | rest] ->
          pickup
            member(h, b) -> diff_go(rest, b, acc)
            else         -> diff_go(rest, b, add(h, acc))
    fn difference(a: Map(t, Bool), b: Map(t, Bool)) -> Map(t, Bool) =
      diff_go(to_list(a), b, new())
  """

  test "Std.Set's rip-out form (parameterised Map + structural recursion) elaborates dependent" do
    assert {:ok, _env} = Program.elaborate(@set_ripout_form)
  end
end
