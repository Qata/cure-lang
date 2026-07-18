defmodule Cure.Elab.ProofSearchTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.ProofSearch
  alias Cure.Core.{Context, Env, Eval, Inductive}

  # A tiny hand-built context: one family P with a single ctor mkP : P, and a
  # local binder h : P in scope. resolve should find `h` by exact type.
  defp env_with_p do
    env = Env.empty()
    family = Inductive.family(:P, [], [], 0)
    ctor = Inductive.ctor(:mkP, [], [])
    Inductive.declare(env, family, [ctor])
  end

  test "a local hypothesis whose type equals the goal is found directly" do
    env = env_with_p()
    goal = {:data, :P, [], []}
    goal_val = Eval.eval(goal, [])
    # Context with a single binder h : P.
    ctx = Context.empty(env) |> Context.extend(goal_val)

    assert {:ok, {:var, 0}} = ProofSearch.resolve(goal, ctx, env)
  end

  test "zero candidates yields :none" do
    env = env_with_p()
    goal = {:data, :P, [], []}
    ctx = Context.empty(env)
    assert :none = ProofSearch.resolve(goal, ctx, env)
  end

  test "two distinct local hypotheses of the goal type are a hard ambiguity error" do
    env = env_with_p()
    goal = {:data, :P, [], []}
    goal_val = Eval.eval(goal, [])
    ctx = Context.empty(env) |> Context.extend(goal_val) |> Context.extend(goal_val)

    assert {:error, {:ambiguous_proof_search, ^goal, provenance}} =
             ProofSearch.resolve(goal, ctx, env)

    assert length(provenance) == 2
  end
end
