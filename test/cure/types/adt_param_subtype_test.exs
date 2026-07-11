defmodule Cure.Types.AdtParamSubtypeTest do
  @moduledoc """
  The classic checker's `subtype?` had no structural rule for two parameterized
  maps (`Map(k, v)` vs `Map(t, Bool)`, resolved to `{:map, k, v}`), so it fell
  through to `false`. That blocked a return-polymorphic extern result
  (`Std.Map.new() : Map(k, v)`) from satisfying a more-specific declared return
  type — which is exactly what parameterizing `Std.Map` to `Map(k, v)` needs, and
  what `Std.Set` (a `Map(t, Bool)`) relies on to compile.

  This pins the covariant rule: key/value are compared pairwise, so a free
  type-var position instantiates (via the existing universal `type_var` rules)
  while a *concrete* position stays strict. The analogous same-constructor rule
  for user ADTs (`{:adt, key, params}`) is covered too.

  This is transitional glue for the classic pipeline (deleted at #18); it keeps
  coexistence green while the parameterized `Std.Map` / map-pattern work lands on
  the dependent side.
  """
  use ExUnit.Case, async: true

  alias Cure.Types.Type

  test "a fully-generic map is a subtype of a more-specific map" do
    generic = {:map, {:type_var, "k"}, {:type_var, "v"}}
    specific = {:map, {:type_var, "t"}, :bool}
    assert Type.subtype?(generic, specific)
  end

  test "an inferred Any-keyed map satisfies a type-var-keyed declaration" do
    assert Type.subtype?({:map, :any, :bool}, {:map, {:type_var, "t"}, :bool})
  end

  test "concrete mismatches in a map param position are still rejected" do
    refute Type.subtype?({:map, :int, :bool}, {:map, :int, :int})
    refute Type.subtype?({:map, :int, :bool}, {:map, :atom, :bool})
  end

  test "same concrete maps are subtypes" do
    assert Type.subtype?({:map, :atom, :int}, {:map, :atom, :int})
  end

  test "the same covariant rule holds for user-defined parameterized ADTs" do
    assert Type.subtype?(
             {:adt, :pair, [{:type_var, "a"}, {:type_var, "b"}]},
             {:adt, :pair, [:int, :bool]}
           )

    refute Type.subtype?({:adt, :pair, [:int, :bool]}, {:adt, :pair, [:int, :int]})
    refute Type.subtype?({:adt, :pair, [:int]}, {:adt, :pair, [:int, :int]})
  end
end
