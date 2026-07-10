defmodule Cure.Core.PrimitiveSeedTest do
  @moduledoc """
  The primitive-type floor (spec 2026-07-10-primitive-type-declarations): every
  seeded env0 resolves the three machine base names to their Core nodes, so bare
  `x: Int` works with no import.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env}

  defp seeded, do: Builtins.seed(Env.empty())

  test "the seed floor binds the three machine base types" do
    env = seeded()
    assert Env.primitive(env, "Int") == {:int_type}
    assert Env.primitive(env, "Float") == {:float_type}
    assert Env.primitive(env, "Binary") == {:binary_type}
  end

  test "a non-primitive name has no primitive binding" do
    assert Env.primitive(seeded(), "Nat") == nil
  end
end
