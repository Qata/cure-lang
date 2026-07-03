defmodule Cure.Core.BuiltinsSeedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  test "seed/1 registers validated bool and nat" do
    env = Builtins.seed(Env.empty())
    assert Inductive.builtin(env, :bool) == :Bool
    assert Inductive.builtin(env, :nat) == :Nat
    assert Inductive.family?(env, :Bool)
    assert Inductive.family?(env, :Nat)
  end

  test "seeded bool family has exactly False and True" do
    env = Builtins.seed(Env.empty())
    names = env |> Inductive.ctors_of(:Bool) |> Enum.map(& &1.name) |> Enum.sort()
    assert names == [:False, :True]
  end

  test "seeded nat family has exactly Z and S/1" do
    env = Builtins.seed(Env.empty())
    ctors = env |> Inductive.ctors_of(:Nat) |> Enum.map(fn c -> {c.name, length(c.args)} end) |> Enum.sort()
    assert ctors == [{:S, 1}, {:Z, 0}]
  end
end
