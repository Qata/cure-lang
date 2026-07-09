defmodule Antigen.Assays.DeltaReduce do
  @moduledoc """
  `delta/nf` — the known-normal-form oracle for δ-reduction (unfolding of
  certified global definitions). Builds the v1 menu extended with two CERTIFIED
  globals, normalizes the challenge term with the trusted `Normalise.nf`, and
  requires the result to equal the correct-by-construction normal form. A
  disagreement is a definitional-equality (δ/ι) soundness infection.

  Certified env: `idnat : Nat -> Nat = λx. x` and `kpair : Σ Nat. Nat = (Z, S Z)`.
  Both are closed and total, so `Env.certify` licenses δ-unfolding — the exact
  precondition `unfold_certified_head` guards on (`Env.certified?` + closed body).
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Context, Env, Normalise}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  # kpair : Sigma(Nat, const-Nat) = mk_pair(Z, S Z) — the inductive dependent pair (D2).
  @kpair_sigma {:data, :Sigma, [@nat, {:lam, @nat, @nat}], []}

  # v1 menu + two certified globals (see moduledoc). Declared here, not in the
  # shared SigMenu, because no other vertical needs global definitions.
  defp env do
    Generators.SigMenu.env_of(:v1)
    |> Env.add_def(:idnat, {:pi, @nat, @nat}, {:lam, @nat, {:var, 0}})
    |> Env.certify(:idnat)
    |> Env.add_def(:kpair, @kpair_sigma, {:ctor, :mk_pair, [@z, {:ctor, :S, [@z]}]})
    |> Env.certify(:kpair)
  end

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :delta_reduce, payload: %{term: term, expected: expected}}) do
    ctx = Context.empty(env())

    case Normalise.nf(ctx, term) do
      ^expected ->
        :ok

      other ->
        {:violation, {:delta_nf_disagreement, %{term: term, expected: expected, got: other}}}
    end
  end
end
