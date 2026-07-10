defmodule Cure.Stdlib.CureStdAnyTest do
  @moduledoc """
  `:cure_std_any` is the runtime backend for `Std.Access`'s `Any` top type.
  Every boundary coercion (`to_any`, `as_map`, `as_list`) `@extern`s to
  `coerce/1`, which must be the identity — the value is unchanged, only its
  Cure-level type is re-ascribed across the typed/untyped boundary.
  """
  use ExUnit.Case, async: true

  test "coerce/1 is the identity on every BEAM term shape" do
    assert :cure_std_any.coerce(42) == 42
    assert :cure_std_any.coerce(:an_atom) == :an_atom
    assert :cure_std_any.coerce(%{a: 1, b: 2}) == %{a: 1, b: 2}
    assert :cure_std_any.coerce([1, 2, 3]) == [1, 2, 3]
    assert :cure_std_any.coerce({:tuple, :shaped}) == {:tuple, :shaped}
    assert :cure_std_any.coerce("string") == "string"
    fun = fn x -> x + 1 end
    assert :cure_std_any.coerce(fun) == fun
  end

  test "coerce/1 preserves identity of the same reference (no copy semantics)" do
    ref = make_ref()
    assert :cure_std_any.coerce(ref) === ref
  end
end
