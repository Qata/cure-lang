defmodule Cure.Elab.Overload do
  @moduledoc """
  Type-directed pruning of an overload set at an applied call site (Ph1, Idris2
  elaborate-and-prune). Pure over an already-elaborated `Env` and the inferred
  argument types; never rewrites Core, never touches the kernel/TCB.

  Given the candidate keys of a bare name (from `Resolution.overload_candidates/2`),
  the inferred argument types, and the written argument labels (Ph2), keep the
  members whose parameter telescope is position-wise convertible to the arguments
  AND whose declared labels agree with the written ones. Exactly one survivor
  resolves; none is `:no_matching_overload`; more than one is
  `:ambiguous_overload`.
  """

  alias Cure.Core.{Env, Grade}

  @spec resolve(Env.t(), atom(), [term()], [String.t() | nil] | nil, [atom()]) ::
          {:ok, atom()}
          | {:error, {:no_matching_overload, atom(), [term()]}}
          | {:error, {:ambiguous_overload, atom(), [String.t()]}}
  def resolve(%Env{} = env, bare, arg_types, written_labels, candidates) do
    survivors =
      Enum.filter(candidates, fn key ->
        case Env.get_def(env, key) do
          %{type: pi} = def ->
            labels_match?(present_labels(def, pi), written_labels) and
              params_match?(env, present_param_types(pi), arg_types)

          _ ->
            false
        end
      end)

    case survivors do
      [key] -> {:ok, key}
      [] -> {:error, {:no_matching_overload, bare, arg_types}}
      many -> {:error, {:ambiguous_overload, bare, owners(many)}}
    end
  end

  @doc """
  Ph2 label check for a SINGLE (non-overloaded) call target. The overload pruner
  above tie-breaks a set by exact label agreement; a lone function instead only
  ENFORCES its declared labels: a mandatory (two-name) label must be written and
  match, while an optional (single-name) label may be omitted or written freely.

  Returns `:ok`, or `{:error, {:label_mismatch, key, declared_present, written}}`
  where both vectors are aligned to the present (non-erased) parameters. A key
  that names no def, or a def with no mandatory labels called without labels, is
  inert `:ok` — keeping every pre-Ph2 call unaffected.
  """
  @spec check_labels(Env.t(), atom(), [String.t() | nil] | nil) ::
          :ok | {:error, {:label_mismatch, atom(), [String.t() | nil], [String.t() | nil] | nil}}
  def check_labels(%Env{} = env, key, written) do
    case Env.get_def(env, key) do
      %{type: pi} = def ->
        declared = present_labels(def, pi)
        if single_labels_ok?(declared, written),
          do: :ok,
          else: {:error, {:label_mismatch, key, declared, written}}

      _ ->
        :ok
    end
  end

  # A lone target's present-param labels versus what the caller wrote. An
  # unwritten call (`written == nil`) is legal only when no present parameter
  # carries a mandatory label — matching every pre-Ph2 def, whose present labels
  # are all `nil`. When labels ARE written, a mandatory (non-nil declared) label
  # must be written identically; an optional (nil declared, single-name) position
  # accepts any written label or none, since the internal binder name the caller
  # may echo is not retained on the def record. A length mismatch defers to the
  # arity machinery rather than double-diagnosing here.
  defp single_labels_ok?(declared, nil), do: Enum.all?(declared, &is_nil/1)

  defp single_labels_ok?(declared, written) when length(declared) == length(written) do
    Enum.zip(declared, written)
    |> Enum.all?(fn
      {nil, _w} -> true
      {d, w} -> d == w
    end)
  end

  defp single_labels_ok?(_declared, _written), do: true

  # A candidate's present-param declared labels must agree with the labels the
  # caller actually wrote. Both vectors are aligned to the PRESENT (non-erased)
  # parameters — the same positions `present_param_types/1` prunes on and the same
  # positions the surface writes arguments for.
  #
  # A written label of `nil` means "no label at this position", so an unwritten
  # call (`written_labels == nil`, the whole common case) matches ONLY a candidate
  # whose present params are all unlabelled — which is every pre-Ph2 def, keeping
  # Ph1 resolution byte-for-byte unchanged. A mandatory external label (`to dest`)
  # is declared non-nil, so it is matched only when the caller writes it; a caller
  # who writes a label a candidate does not declare prunes that candidate.
  defp labels_match?(declared_present, nil), do: Enum.all?(declared_present, &is_nil/1)

  defp labels_match?(declared_present, written),
    do: length(declared_present) == length(written) and declared_present == written

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

  # The declared external labels of a candidate's PRESENT parameters, in order —
  # the label vector stored on the def record (telescope-aligned, full length),
  # restricted to the same non-erased positions `present_param_types/1` keeps. A
  # label-free def carries no vector, so every present position is `nil`.
  defp present_labels(def, pi) do
    grades = pi_grades(pi)
    full = def_labels(def, length(grades))

    grades
    |> Enum.zip(full)
    |> Enum.filter(fn {g, _l} -> Grade.present?(g) end)
    |> Enum.map(fn {_g, l} -> l end)
  end

  defp pi_grades({:pi, grade, _domain, codomain}), do: [grade | pi_grades(codomain)]
  defp pi_grades(_return), do: []

  defp def_labels(def, arity) do
    case Map.get(def, :labels) do
      nil -> List.duplicate(nil, arity)
      labels -> labels
    end
  end

  # Whether a Core term mentions any de Bruijn variable — i.e. a parameter type
  # that depends on an earlier telescope binder. Cheap structural scan over the
  # tuple/list term representation.
  defp mentions_var?({:var, _}), do: true
  defp mentions_var?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&mentions_var?/1)
  defp mentions_var?(l) when is_list(l), do: Enum.any?(l, &mentions_var?/1)
  defp mentions_var?(_leaf), do: false

  defp owners(keys), do: keys |> Enum.map(&Cure.Elab.Name.owner/1) |> Enum.uniq()
end
