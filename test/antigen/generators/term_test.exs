defmodule Antigen.Generators.TermTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  @doc false
  def sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "every intro-fragment term checks at its goal (soundness over the fragment)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for goal <- SigMenu.goal_types() do
      for t <- sample(Term.gen_term(ctx, goal), 40) do
        {:ok, ty} = Kernel.infer(ctx, t)
        assert Kernel.check(ctx, t, ty) == :ok
      end
    end
  end

  test "a Pi goal yields a lambda" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    goal = {:pi, SigMenu.nat(), SigMenu.nat()}
    ts = sample(Term.gen_term(ctx, goal), 40)
    assert Enum.any?(ts, &match?({:lam, _, _}, &1))
    for t <- ts, do: assert {:ok, _} = Kernel.infer(ctx, t)
  end

  test "a Type 0 goal yields a menu type former (the {:type,_} intro row)" do
    # `{:type, 0}` is never drawn as a goal by `Term.typed_term/1`'s `goal_gen`
    # (Task 6) or by `Generators.Context` (Task 2) — see the goal-space note
    # after Task 6 — so this is the ONLY place the `{:type,_}` clause of
    # `intro_rules` (and its var/INDIR-only elimination companions) gets
    # exercised at all. Without this test the clause would ship with zero
    # coverage.
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    goal = {:type, 0}
    ts = sample(Term.gen_term(ctx, goal), 40)
    assert Enum.all?(ts, &(&1 in [SigMenu.nat(), SigMenu.bd(), SigMenu.vec({:ctor, :Z, []})]))
    for t <- ts, do: assert {:ok, _} = Kernel.infer(ctx, t)
  end
end
