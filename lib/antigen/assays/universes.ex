defmodule Antigen.Assays.Universes do
  @moduledoc """
  `universes` (pre-port banking spec §4 W5). Oracle = the known label. Def-shaped
  challenges run `Kernel.check_def`; family-shaped ones run `Kernel.check_family`
  plus `Kernel.check_ctor` per constructor. The kernel must accept iff
  `:well_typed`: an accepted `:ill_typed` (e.g. Type-in-Type) is a soundness
  infection; a rejected `:well_typed` (e.g. cumulativity) is an incompleteness bug.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Env, Inductive, Kernel}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :indexed_case, label: label, payload: %{def_name: dn}} = c) do
    env = Generators.Universes.env_of(c)
    judge(label, Kernel.check_def(env, dn), dn)
  end

  def run(%Challenge{kind: :family, label: label, payload: %{family: fam, ctors: ctors}}) do
    env = Inductive.declare(Env.empty(), fam, ctors)

    verdict =
      with :ok <- Kernel.check_family(env, fam) do
        Enum.reduce_while(ctors, :ok, fn ctor, :ok ->
          case Kernel.check_ctor(env, fam, ctor) do
            :ok -> {:cont, :ok}
            {:error, _} = err -> {:halt, err}
          end
        end)
      end

    judge(label, verdict, fam.name)
  end

  defp judge(:well_typed, :ok, _n), do: :ok
  defp judge(:ill_typed, {:error, _}, _n), do: :ok
  defp judge(:well_typed, {:error, reason}, n), do: {:violation, {:wrongly_rejected, {n, reason}}}
  defp judge(:ill_typed, :ok, n), do: {:violation, {:wrongly_accepted, n}}
end
