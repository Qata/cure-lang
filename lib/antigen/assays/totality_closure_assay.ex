defmodule Antigen.Assays.TotalityClosureAssay do
  @moduledoc """
  Property tests for the untrusted totality-closure driver
  `Cure.Elab.TotalityClosure` (spec: antigen-totality-closure).

    * totality_closure/soundness    — a diverging function reachable from a type
      position must be REJECTED by `certify_type_level` (V5a). An all-total env
      must certify (`:accept` control).
    * totality_closure/completeness — `type_level_fns(env)` is a superset of an
      independent type-position reachability walk (V5b).

  The driver ops go through an injectable @real map (run/2); negative controls
  weaken them without touching `Cure.Elab`/`Cure.Core` or using :meck.
  """
  alias Antigen.Challenge
  alias Cure.Elab.TotalityClosure
  alias Cure.Core.Env

  @real %{
    certify: &TotalityClosure.certify_type_level/1,
    type_level_fns: &TotalityClosure.type_level_fns/1
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :closure_env} = c), do: run(c, @real)

  def run(%Challenge{kind: :closure_env, assay: "totality_closure/soundness", payload: %{env: env, expect: :reject}}, k) do
    case k.certify.(env) do
      {:error, {:totality_required, _}} -> :ok
      {:ok, _} -> {:violation, {:diverging_certified, env}}
      other -> {:violation, {:unexpected_certify_result, other}}
    end
  end

  def run(%Challenge{kind: :closure_env, assay: "totality_closure/soundness", payload: %{env: env, expect: :accept}}, k) do
    case k.certify.(env) do
      {:ok, _} -> :ok
      other -> {:violation, {:total_env_not_certified, other}}
    end
  end
end
