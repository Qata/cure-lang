defmodule Antigen.Coverage do
  @moduledoc "The coverage key: a plateauing feature vector for dedup + the health gate (spec §7.2, §9)."
  alias Antigen.Challenge

  @elim_flags %{app: :app_present, case: :case_present, fst: :fst_present,
                snd: :snd_present, rewrite: :rewrite_present}

  @spec key(Challenge.t()) :: {MapSet.t(atom()), atom(), MapSet.t(atom()), Challenge.label()}
  def key(%Challenge{} = c) do
    terms = terms_of(c)
    ctors = terms |> Enum.flat_map(&constructors/1) |> MapSet.new()
    depth = terms |> Enum.map(&depth/1) |> Enum.max(fn -> 0 end)
    flags = flags(c, terms, ctors)
    {ctors, bucket(depth), flags, c.label}
  end

  @spec key_string({MapSet.t(), atom(), MapSet.t(), atom()}) :: String.t()
  def key_string({ctors, bucket, flags, label}) do
    cs = ctors |> Enum.sort() |> Enum.join(",")
    fs = flags |> Enum.sort() |> Enum.join(",")
    "ctors=[#{cs}]|depth=#{bucket}|flags=[#{fs}]|label=#{label}"
  end

  @spec terms_of(Challenge.t()) :: [Cure.Core.Term.t()]
  def terms_of(%Challenge{kind: :stub, payload: %{term: t}}), do: [t]
  # Phase 2 adds :def_group / :family / :forcing_pair clauses (Tasks 9–11).

  defp bucket(d) when d <= 2, do: :b0_2
  defp bucket(d) when d <= 5, do: :b3_5
  defp bucket(d) when d <= 9, do: :b6_9
  defp bucket(_), do: :b10p

  defp flags(%Challenge{kind: kind}, terms, ctors) do
    base = for {c, flag} <- @elim_flags, MapSet.member?(ctors, c), into: MapSet.new(), do: flag
    base = if kind in [:def_group, :forcing_pair], do: MapSet.put(base, :has_mutual_group), else: base
    base = if Enum.any?(terms, &has_shadowing?/1), do: MapSet.put(base, :has_shadowing), else: base
    base
  end

  # `:has_shadowing` (spec §7.2): a coarse approximation — any `:lam`/`:pi`/`:sigma`
  # binder nested underneath another such binder. A single top-level binder does
  # not count; only nesting (e.g. a curried `{:pi, _, {:pi, _, _}}`) does.
  defp has_shadowing?(t), do: nested_binder?(t, false)

  defp nested_binder?(t, inside?) when is_tuple(t) do
    tag = elem(t, 0)
    binder? = tag in [:lam, :pi, :sigma]
    here = binder? and inside?
    children = t |> Tuple.to_list() |> tl()
    here or Enum.any?(children, fn c -> nested_binder?(c, inside? or binder?) end)
  end

  defp nested_binder?(list, inside?) when is_list(list), do: Enum.any?(list, &nested_binder?(&1, inside?))
  defp nested_binder?(_, _), do: false

  # structural helpers over the tagged-tuple AST
  defp constructors(t), do: fold(t, [], fn node, acc -> [tag(node) | acc] end) |> Enum.reject(&is_nil/1)
  defp depth(t), do: fold_depth(t)
  defp tag(t) when is_tuple(t), do: elem(t, 0)
  defp tag(_), do: nil

  defp fold(t, acc, f) when is_tuple(t) do
    acc = f.(t, acc)
    t |> Tuple.to_list() |> Enum.reduce(acc, fn child, a -> fold(child, a, f) end)
  end

  defp fold(list, acc, f) when is_list(list), do: Enum.reduce(list, acc, fn c, a -> fold(c, a, f) end)
  defp fold(_leaf, acc, _f), do: acc

  # A node's depth is 1 + the max depth of its *term-shaped* children (nested
  # tuples/lists); non-term children (the leading tag atom, bare integers/de
  # Bruijn indices, plain atoms) don't count, so a primitive leaf like
  # `{:type, 0}` or `{:var, 0}` has depth 0, not 1 — verified against the
  # Step-1 fixtures: `{:app, {:lam, {:type,0}, {:var,0}}, {:type,0}}` computes
  # to depth 2 (bucket `:b0_2`) and the four-`:app` `deep` fixture computes to
  # depth 3 (bucket `:b3_5`).
  defp fold_depth(t) when is_tuple(t) do
    child_depths =
      t
      |> Tuple.to_list()
      |> Enum.filter(&(is_tuple(&1) or is_list(&1)))
      |> Enum.map(&fold_depth/1)

    case child_depths do
      [] -> 0
      ds -> 1 + Enum.max(ds)
    end
  end

  defp fold_depth(list) when is_list(list), do: Enum.max([0 | Enum.map(list, &fold_depth/1)])
  defp fold_depth(_), do: 0
end
