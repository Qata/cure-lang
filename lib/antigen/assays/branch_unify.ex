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
  alias Cure.Core.{Context, Eval, Inductive, Kernel}

  @nat_type {:vdata, :Nat, []}
  @nat {:data, :Nat, [], []}

  # v1 menu extended with a crossing 4-index family `Cyc4` whose constructor
  # `mkcyc : (a b : Nat) -> Cyc4 a a b b` induces a multi-key unification cycle
  # (`i := j`, later `j := i`) when matched against a crossing scrutinee
  # `Cyc4 i j j i` — the spec §4.1 resolve-before-bind obligation. Not in the shared
  # v1 menu (no other generator needs it), so it is declared here.
  defp env do
    Generators.SigMenu.env_of(:v1)
    |> Inductive.declare(
      Inductive.family(:Cyc4, [], [{:i, @nat}, {:j, @nat}, {:k, @nat}, {:l, @nat}], 0),
      [Inductive.ctor(:mkcyc, [{:a, @nat}, {:b, @nat}], [{:var, 1}, {:var, 1}, {:var, 0}, {:var, 0}])]
    )
  end

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :branch_unify, label: expected, payload: p}) do
    env = env()

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
