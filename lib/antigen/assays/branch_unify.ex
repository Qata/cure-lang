defmodule Antigen.Assays.BranchUnify do
  @moduledoc """
  `branchunify/verdict` — the known-label oracle for the kernel's index-refinement
  unifier. Builds a v1-menu context with `ctx_vars` outer `Nat` variables, evaluates
  the scrutinee index terms to values, and asks `Cure.Core.Kernel.branch_unify/4`
  to refine; the returned verdict category (`:trivial` | `:solved` | `:impossible`)
  must match the correct-by-construction label. A disagreement is an
  index-unification soundness/completeness infection.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Context, Eval, Kernel}

  @nat_type {:vdata, :Nat, []}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :branch_unify, label: expected, payload: p}) do
    env = Generators.SigMenu.env_of(:v1)

    ctx =
      Enum.reduce(1..p.ctx_vars//1, Context.empty(env), fn _, c ->
        Context.extend(c, @nat_type)
      end)

    index_vals = Enum.map(p.indices, &Eval.eval(&1, Context.env(ctx)))

    category =
      case Kernel.branch_unify(ctx, p.dname, p.cname, index_vals) do
        {:solved, _} -> :solved
        other -> other
      end

    if category == expected do
      :ok
    else
      {:violation, {:branch_unify_disagreement, %{payload: p, expected: expected, got: category}}}
    end
  end
end
