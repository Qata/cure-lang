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

  # -- Tier-B reach expansion: List(A) parametric family (Task 1) --------------

  test "env_of(:v1) registers the List(A) family with Nil/Cons" do
    env = SigMenu.env_of(:v1)
    assert Inductive.param_count(env, :List) == 1
    assert Inductive.ctor_quantities(env, :Nil) != nil
    assert Inductive.ctor_quantities(env, :Cons) != nil
  end

  test "List(Nat) is inhabitable and canon gives Nil" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [SigMenu.nat()], []}
    assert SigMenu.inhabitable?(ctx, list_nat)
    assert SigMenu.canon(ctx, list_nat) == {:ctor, :Nil, []}
  end

  # The only Task-1 test that exercises the kernel on a param-bearing checking-mode
  # term — the one that catches a missing/wrong `result_params`. List is check-mode-
  # only at the top level (a bare param-ctor never infers — kernel.ex), so wrap in
  # an identity application (same trick Task 6/8 use).
  test "Cons/Nil check-mode-accept against List(Nat) (result_params correctness)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [SigMenu.nat()], []}
    nil_wrapped = {:app, {:lam, list_nat, {:var, 0}}, {:ctor, :Nil, []}}
    cons_wrapped = {:app, {:lam, list_nat, {:var, 0}},
                    {:ctor, :Cons, [{:ctor, :Z, []}, {:ctor, :Nil, []}]}}
    assert {:ok, _} = Kernel.infer(ctx, nil_wrapped)
    assert {:ok, _} = Kernel.infer(ctx, cons_wrapped)
  end
end
