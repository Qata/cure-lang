defmodule Antigen.Generators.SigMenuTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Env, Inductive, Context, Kernel}

  test "env_of(:v1) certifies plus and dbl through the real certifier" do
    env = SigMenu.env_of(:v1)
    assert Env.certified?(env, :plus)
    assert Env.certified?(env, :dbl)
    # families present (get_family/2 is on Inductive, not Env — see Reference)
    assert Inductive.get_family(env, :Nat)
    assert Inductive.get_family(env, :Bd)
    assert Inductive.get_family(env, :Vec)
  end

  test "canon builds a well-typed inhabitant for each closed goal type" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for goal <- SigMenu.goal_types() do
      assert SigMenu.inhabitable?(ctx, goal)
      term = SigMenu.canon(ctx, goal)
      {:ok, ty} = Kernel.infer(ctx, term)
      # inferred value must convert with the goal at top level
      assert Kernel.check(ctx, term, ty) == :ok
    end
  end

  test "canon handles a stuck-indexed Vec via a matching context variable" do
    env = SigMenu.env_of(:v1)
    # Γ = [ n : Nat, xs : Vec(n) ]  (kernel order: xs innermost = index 0)
    ctx = SigMenu.rebuild_context(env, [SigMenu.vec({:var, 0}), SigMenu.nat()])
    goal = SigMenu.vec({:var, 1})       # Vec(n), n = index 1 from the body
    assert SigMenu.inhabitable?(ctx, goal)
    term = SigMenu.canon(ctx, goal)
    assert {:ok, _} = Kernel.infer(ctx, term)
  end
end
