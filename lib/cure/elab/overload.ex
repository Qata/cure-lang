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

  # A lone target's present-param label descriptors versus what the caller wrote.
  # An unwritten call (`written == nil`) is legal only when no present parameter
  # carries a MANDATORY label — matching every pre-Ph2 def, whose present params
  # are all `{:optional, _}`. When labels ARE written, each position is checked by
  # `label_pos_ok?/2`: a mandatory label must be written identically; an optional
  # one may be omitted or written with the retained binder name (a label naming no
  # parameter is rejected). A length mismatch defers to the arity machinery rather
  # than double-diagnosing here (so `single_labels_ok?/2` and the pruning
  # `labels_match?/2` differ ONLY at that last clause).
  defp single_labels_ok?(declared, nil), do: not Enum.any?(declared, &mandatory?/1)

  defp single_labels_ok?(declared, written) when length(declared) == length(written) do
    Enum.zip(declared, written) |> Enum.all?(fn {d, w} -> label_pos_ok?(d, w) end)
  end

  defp single_labels_ok?(_declared, _written), do: true

  # A candidate's present-param label descriptors must agree with the labels the
  # caller actually wrote. Both vectors are aligned to the PRESENT (non-erased)
  # parameters — the same positions `present_param_types/1` prunes on and the same
  # positions the surface writes arguments for.
  #
  # An unwritten call (`written_labels == nil`, the whole common case) matches ONLY
  # a candidate with no mandatory present label — every pre-Ph2 def is
  # all-`{:optional, _}`, keeping Ph1 resolution unchanged. When labels are
  # written, each position is checked by `label_pos_ok?/2`: a mandatory external
  # label (`to dest`) matches only when the caller writes it; an optional
  # (single-name) label matches when omitted OR written with the parameter's own
  # binder name (`describe(x: 5)` for `fn describe(x: Int)` — the SAME call as
  # `describe(5)`, spec §3/§5). A written label naming NO parameter prunes the
  # candidate, and a length mismatch is a non-match (wrong arity for this member).
  defp labels_match?(declared_present, nil), do: not Enum.any?(declared_present, &mandatory?/1)

  defp labels_match?(declared_present, written) when length(declared_present) == length(written) do
    Enum.zip(declared_present, written) |> Enum.all?(fn {d, w} -> label_pos_ok?(d, w) end)
  end

  defp labels_match?(_declared_present, _written), do: false

  # Whether a parameter's label descriptor makes writing the label mandatory.
  defp mandatory?({:required, _label}), do: true
  defp mandatory?(_optional), do: false

  # Whether the label the caller wrote at one position (`w`, possibly `nil`) is
  # allowed by that parameter's descriptor. A mandatory label must be written
  # exactly; an optional one may be omitted or written with the parameter's own
  # binder name; an optional position whose name was not recorded stays lenient.
  defp label_pos_ok?({:required, label}, w), do: w == label
  defp label_pos_ok?({:optional, nil}, _w), do: true
  defp label_pos_ok?({:optional, name}, w), do: is_nil(w) or w == name

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

  # The label descriptors of a candidate's PRESENT parameters, in order — the
  # vector stored on the def record (telescope-aligned, full length), restricted
  # to the same non-erased positions `present_param_types/1` keeps. A def with no
  # stored vector defaults to `{:optional, nil}` at every position (lenient, no
  # mandatory label), so pre-Ph2 defs are unaffected.
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
      nil -> List.duplicate({:optional, nil}, arity)
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
