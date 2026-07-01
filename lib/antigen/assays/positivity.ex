defmodule Antigen.Assays.Positivity do
  @moduledoc """
  `positivity` (spec §4.2). Oracle = the known label. The kernel must accept a
  family iff it is strictly positive: a labeled-negative family that is accepted,
  or a labeled-positive family that is rejected, is an infection.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.Inductive

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :family, label: label, payload: %{family: fam}} = c) do
    env = Generators.Positivity.env_of(c)
    verdict = Inductive.positive?(env, Inductive.get_family(env, fam.name))

    case {label, verdict} do
      {:positive, :ok} -> :ok
      {:negative, {:error, _}} -> :ok
      {:positive, {:error, reason}} -> {:violation, {:wrongly_rejected, reason}}
      {:negative, :ok} -> {:violation, {:wrongly_accepted, fam.name}}
    end
  end
end
