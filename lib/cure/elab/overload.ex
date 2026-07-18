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

  alias Cure.Core.{Env, Grade}

  @spec resolve(Env.t(), atom(), [term()], [atom()]) ::
          {:ok, atom()}
          | {:error, {:no_matching_overload, atom(), [term()]}}
          | {:error, {:ambiguous_overload, atom(), [String.t()]}}
  def resolve(%Env{} = env, bare, arg_types, candidates) do
    survivors =
      Enum.filter(candidates, fn key ->
        case Env.get_def(env, key) do
          %{type: pi} -> params_match?(env, present_param_types(pi), arg_types)
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
      # A polymorphic/dependent present param (one still mentioning a telescope
      # binder — e.g. `List(t)` under an erased `{t: Type}`, or `Vec(n)` under a
      # value `n`) cannot be decided by first-order conversion here, because the
      # binder is not yet instantiated to the argument. Conservatively KEEP such a
      # candidate rather than pruning it: this errs toward ambiguity (the caller
      # qualifies), never toward a silent wrong unique pick. A ground param is
      # decided by ordinary convertibility.
      mentions_var?(p) or Cure.Elab.TypeConv.convertible?(env, p, a)
    end)
  end

  # The PRESENT (non-erased) parameter domains of the stored Pi type, in order.
  # An erased leading implicit (`{t: Type}`, grade 0 — e.g. the `t` of a
  # polymorphic `Std.List#length : {t} -> List(t) -> Nat`) carries no runtime
  # argument and no inferred arg type to prune against, so it is dropped: the
  # present-param arity then matches the present-argument arity that
  # `map_present_args/4` produced. Value- and type-domains alike are kept when
  # present — NOT the `typealias_parameter_count` shape, whose `{:type, _level}`
  # guard would drop ordinary value-typed domains like `Meters`/`Grams`.
  defp present_param_types({:pi, grade, domain, codomain}) do
    rest = present_param_types(codomain)
    if Grade.present?(grade), do: [domain | rest], else: rest
  end

  defp present_param_types(_return), do: []

  # Whether a Core term mentions any de Bruijn variable — i.e. a parameter type
  # that depends on an earlier telescope binder. Cheap structural scan over the
  # tuple/list term representation.
  defp mentions_var?({:var, _}), do: true
  defp mentions_var?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&mentions_var?/1)
  defp mentions_var?(l) when is_list(l), do: Enum.any?(l, &mentions_var?/1)
  defp mentions_var?(_leaf), do: false

  defp owners(keys), do: keys |> Enum.map(&Cure.Elab.Name.owner/1) |> Enum.uniq()
end
