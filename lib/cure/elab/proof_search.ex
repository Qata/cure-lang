defmodule Cure.Elab.ProofSearch do
  @moduledoc """
  Auto proof-search over `@lemma`-tagged theorems and local hypotheses
  (design: docs/superpowers/specs/2026-07-18-auto-lemma-proof-search-design.md).

  Untrusted: only *builds* Core proof terms; every candidate is re-checked by
  the kernel (`Cure.Core.Kernel.check/3`), so search can never make an
  ill-typed program type-check.
  """
  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.{MetaCtx, Unify, Subst}

  @type goal :: term()
  @type result :: {:ok, term()} | :none | {:error, {:ambiguous_proof_search, term(), [term()]}}

  # Search terminates on two conditions: a recursion-depth ceiling and a
  # per-branch "already trying this goal" cycle stack.
  @depth_limit 5

  @spec resolve(goal(), Context.t(), Cure.Core.Env.t()) :: result()
  def resolve(goal, ctx, env), do: resolve(goal, ctx, env, %{depth: 0, trying: []})

  # Depth-bound guard: abandon a branch that has descended past the ceiling.
  def resolve(_goal, _ctx, _env, %{depth: d}) when d > @depth_limit, do: :none

  # Cycle guard: if this goal is already being attempted higher on the branch,
  # abandon it (a self-referential lemma set would otherwise loop forever).
  def resolve(goal, ctx, env, %{trying: ts} = state) do
    if Enum.any?(ts, &same_goal?(&1, goal, ctx, env)) do
      :none
    else
      candidates =
        local_candidates(goal, ctx, env) ++
          projection_candidates(goal, ctx, env) ++
          lemma_candidates(goal, ctx, env, state)

      decide(candidates, goal)
    end
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

  # Refinement/Sigma second-projection search: for every local binder whose type
  # WHNFs to the Sigma family, the binder's `.2` projection proves the predicate
  # about its first component. Its type `P(sigma_first(binder))` is checked
  # against the goal by the kernel.
  defp projection_candidates(goal, ctx, env) do
    goal_val = Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    for k <- 0..(len - 1)//1, len > 0 do
      case sigma_params(Context.lookup(ctx, k), ctx, env) do
        {:ok, a_value, predicate_value} ->
          term = sigma_second_of({:var, k}, a_value, predicate_value, ctx)

          case Kernel.check(ctx, term, goal_val) do
            :ok -> {term, {:projection, k}}
            _ -> {nil, {:projection, k}}
          end

        :error ->
          {nil, {:projection, k}}
      end
    end
    |> Enum.filter(fn {term, _} -> term != nil end)
  end

  # If a Value WHNFs to the Sigma family, return its two params
  # `{:ok, a_value, predicate_value}`; else `:error`. Sigma has exactly two
  # params (`a: Type`, `b: (a) -> Type`) and zero indices.
  defp sigma_params(nil, _ctx, _env), do: :error

  defp sigma_params(type_value, ctx, env) do
    case Cure.Core.Inductive.builtin(env, :sigma) do
      nil ->
        :error

      sigma_fam ->
        case Cure.Core.Normalise.whnf_value(type_value, Context.signature(ctx)) do
          {:vdata, ^sigma_fam, [a_value, predicate_value]} -> {:ok, a_value, predicate_value}
          _ -> :error
        end
    end
  end

  # `{:var,k}.2` — sigma_second applied with its implicit `{a}`/`{predicate}`
  # arguments reified DIRECTLY from the Sigma family's own params (not fresh
  # metavars: those never reach the kernel; sigma_params/3 already pinned down
  # `a_value`/`predicate_value` from the binder's own type). The assembled term
  # is meta-free before it reaches Kernel.check.
  defp sigma_second_of(var_term, a_value, predicate_value, ctx) do
    depth = Context.length(ctx)
    sig = Context.signature(ctx)
    a_term = Cure.Core.Quote.reify(a_value, depth, sig)
    predicate_term = Cure.Core.Quote.reify(predicate_value, depth, sig)
    build_app({:global, :sigma_second}, [a_term, predicate_term, var_term])
  end

  # Lemma-application search: every registered lemma under the goal's head whose
  # conclusion unifies with the goal, with any explicit-hypothesis sub-goals
  # resolved recursively, assembled into a curried application and kernel-checked.
  defp lemma_candidates(goal, ctx, env, state) do
    case head_of(goal) do
      nil ->
        []

      head ->
        env
        |> Cure.Core.Env.lemmas(head)
        |> Enum.map(&try_lemma(&1, goal, ctx, env, state))
        |> Enum.filter(fn {term, _} -> term != nil end)
    end
  end

  defp head_of({:data, name, _p, _i}), do: name
  defp head_of(_), do: nil

  # Instantiate the lemma's Pi telescope with metavars, unify the conclusion
  # with the goal, resolve unsolved (explicit-hypothesis) binders as sub-goals,
  # assemble the application, and kernel-check it.
  defp try_lemma(%{name: name, type: pi}, goal, ctx, env, state) do
    mctx = MetaCtx.new()
    {arg_metas, conclusion, mctx} = instantiate_telescope(pi, mctx)

    with {:ok, mctx} <- Unify.unify(conclusion, goal, mctx, env),
         {:ok, args} <- fill_args(arg_metas, ctx, env, mctx, state) do
      term = build_app({:global, name}, args)
      goal_val = Eval.eval(goal, Context.env(ctx))

      case Kernel.check(ctx, term, goal_val) do
        :ok -> {term, {:lemma, name}}
        _ -> {nil, {:lemma, name}}
      end
    else
      _ -> {nil, {:lemma, name}}
    end
  end

  # Peel every {:pi,g,dom,cod}; for each binder mint a fresh metavar and
  # instantiate it into cod. Returns {arg-metas-with-domains, conclusion, mctx}.
  defp instantiate_telescope(pi, mctx), do: instantiate_telescope(pi, mctx, [])

  defp instantiate_telescope({:pi, _g, dom, cod}, mctx, acc) do
    {mctx, id} = MetaCtx.fresh(mctx, nil)
    meta = {:meta, id}
    cod2 = Subst.instantiate(cod, [meta])
    instantiate_telescope(cod2, mctx, [{meta, dom} | acc])
  end

  defp instantiate_telescope(conclusion, mctx, acc),
    do: {Enum.reverse(acc), conclusion, mctx}

  # For each telescope slot: if its metavar is solved by conclusion-unification,
  # use the solution; otherwise treat the (zonked) domain as a sub-goal and recurse.
  defp fill_args(arg_metas, ctx, env, mctx, state) do
    Enum.reduce_while(arg_metas, {:ok, []}, fn {meta, dom}, {:ok, acc} ->
      z = Unify.zonk(meta, mctx)

      if solved?(z) do
        {:cont, {:ok, acc ++ [z]}}
      else
        subgoal = Unify.zonk(dom, mctx)
        subgoal_core = ensure_core(subgoal, ctx)

        case resolve(subgoal_core, ctx, env, deeper(state, subgoal_core)) do
          {:ok, term} -> {:cont, {:ok, acc ++ [term]}}
          _ -> {:halt, :fail}
        end
      end
    end)
    |> case do
      {:ok, args} -> {:ok, args}
      :fail -> :fail
    end
  end

  defp solved?({:meta, _}), do: false
  defp solved?(_), do: true

  defp build_app(head, args), do: Enum.reduce(args, head, fn a, f -> {:app, f, a} end)

  # Descend one level: increment depth and push the sub-goal onto the cycle stack.
  defp deeper(%{depth: d, trying: ts}, subgoal), do: %{depth: d + 1, trying: [subgoal | ts]}

  # A sub-goal produced by zonk/reify is already a Core term.
  defp ensure_core(term, _ctx), do: term

  # Up-to-conversion equality of two goal Core terms. `Conv.conv?/5` takes Core
  # terms and evaluates them itself, so pass the terms directly (not pre-evaled).
  defp same_goal?(a, b, ctx, env) do
    Cure.Core.Conv.conv?(a, b, Context.env(ctx), Context.length(ctx), env)
  end
end
