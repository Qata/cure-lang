defmodule Cure.Elab.ProofSearch do
  @moduledoc """
  Auto proof-search over `@lemma`-tagged theorems and local hypotheses
  (design: docs/superpowers/specs/2026-07-18-auto-lemma-proof-search-design.md).

  Untrusted: only *builds* Core proof terms; every candidate is re-checked by
  the kernel (`Cure.Core.Kernel.check/3`), so search can never make an
  ill-typed program type-check.
  """
  alias Cure.Core.{Context, Eval, Kernel}

  @type goal :: term()
  @type result :: {:ok, term()} | :none | {:error, {:ambiguous_proof_search, term(), [term()]}}

  @spec resolve(goal(), Context.t(), Cure.Core.Env.t()) :: result()
  def resolve(goal, ctx, env), do: resolve(goal, ctx, env, %{depth: 0, trying: []})

  # Extended entrypoint (Task 6 fills in depth/cycle guards).
  def resolve(goal, ctx, env, _state) do
    candidates = local_candidates(goal, ctx, env)
    decide(candidates, goal)
  end

  # Each candidate is {term, provenance}. Keep only the kernel-checked survivors.
  defp decide(candidates, goal) do
    survivors = Enum.filter(candidates, fn {term, _prov} -> term != nil end)

    case survivors do
      [] -> :none
      [{term, _}] -> {:ok, term}
      many -> {:error, {:ambiguous_proof_search, goal, Enum.map(many, &elem(&1, 1))}}
    end
  end

  # Local-context search: every binder whose type checks against the goal.
  defp local_candidates(goal, ctx, _env) do
    goal_val = Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    if len > 0 do
      for k <- 0..(len - 1)//1 do
        term = {:var, k}

        case Kernel.check(ctx, term, goal_val) do
          :ok -> {term, {:local, k}}
          _ -> {nil, {:local, k}}
        end
      end
      |> Enum.filter(fn {term, _} -> term != nil end)
    else
      []
    end
  end
end
