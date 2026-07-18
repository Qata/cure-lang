defmodule Cure.Elab.Overload do
  @moduledoc """
  Type-directed pruning of an overload set at an applied call site (Ph1, Idris2
  elaborate-and-prune). Pure over an already-elaborated `Env` and the inferred
  argument types; never rewrites Core, never touches the kernel/TCB.

  Given the candidate keys of a bare name (from `Resolution.overload_candidates/2`)
  and the inferred argument types, keep the members whose parameter telescope is
  position-wise convertible to the arguments. Exactly one survivor resolves; none
  is `:no_matching_overload`; more than one is `:ambiguous_overload`.
  """

  alias Cure.Core.Env

  @spec resolve(Env.t(), atom(), [term()], [atom()]) ::
          {:ok, atom()}
          | {:error, {:no_matching_overload, atom(), [term()]}}
          | {:error, {:ambiguous_overload, atom(), [String.t()]}}
  def resolve(%Env{} = env, bare, arg_types, candidates) do
    survivors =
      Enum.filter(candidates, fn key ->
        case Env.get_def(env, key) do
          %{type: pi} -> params_match?(env, param_types(pi), arg_types)
          _ -> false
        end
      end)

    case survivors do
      [key] -> {:ok, key}
      [] -> {:error, {:no_matching_overload, bare, arg_types}}
      many -> {:error, {:ambiguous_overload, bare, owners(many)}}
    end
  end

  defp params_match?(_env, ptypes, atypes) when length(ptypes) != length(atypes), do: false

  defp params_match?(env, ptypes, atypes) do
    Enum.all?(Enum.zip(ptypes, atypes), fn {p, a} ->
      Cure.Elab.TypeConv.convertible?(env, p, a)
    end)
  end

  # Every parameter domain of the stored Pi type, in order. Collects each domain
  # unconditionally (value- and type-domains alike) — NOT the
  # `typealias_parameter_count` shape, whose `{:type, _level}` guard would drop
  # ordinary value-typed domains like `Meters`/`Grams`.
  defp param_types({:pi, _grade, domain, codomain}), do: [domain | param_types(codomain)]
  defp param_types(_return), do: []

  defp owners(keys), do: keys |> Enum.map(&Cure.Elab.Name.owner/1) |> Enum.uniq()
end
