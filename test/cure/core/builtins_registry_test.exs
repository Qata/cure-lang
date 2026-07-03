defmodule Cure.Core.BuiltinsRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive}

  test "register_builtin binds a key resolvable by builtin/2" do
    env = Inductive.register_builtin(Env.empty(), :bool, :Bool)
    assert Inductive.builtin(env, :bool) == :Bool
  end

  test "builtin/2 returns nil for an unbound key" do
    assert Inductive.builtin(Env.empty(), :bool) == nil
  end

  test "a second registration of the same key is a hard error" do
    env = Inductive.register_builtin(Env.empty(), :bool, :Bool)
    assert_raise ArgumentError, ~r/already bound/, fn ->
      Inductive.register_builtin(env, :bool, :OtherBool)
    end
  end
end
