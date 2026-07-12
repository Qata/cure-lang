# lib/cure/compiler/macro_validate.ex
defmodule Cure.Compiler.MacroValidate do
  @moduledoc """
  Frontend validation of `macro` definitions against the self-proving
  obligations (design 2026-07-11 §3). TCB delta zero — pure analysis over the
  parsed `{:macro_def, …}` AST, upstream of the elaborator.
  """

  @type point :: {:hole_kind, String.t()} | {:keyword, String.t()} | {:failure, String.t()}

  @doc """
  Check a macro's `explain` block covers every structural failure point derived
  from its `syntax`/`literal` rules (design §3.2). Returns `:ok` or
  `{:error, {:missing_diagnosis, uncovered_points}}`.
  """
  @spec check_explain_exhaustive(tuple()) :: :ok | {:error, {:missing_diagnosis, [point]}}
  def check_explain_exhaustive({:macro_def, _meta, rules}) do
    points = derive_points(rules)
    covered = covered_points(rules)

    case Enum.reject(points, &covered?(&1, covered)) do
      [] -> :ok
      uncovered -> {:error, {:missing_diagnosis, uncovered}}
    end
  end

  @doc """
  Check every `syntax` rule carries at least one worked example (design §5.1).
  Returns `:ok` or `{:error, {:rule_unpinned, unpinned_keywords}}`.
  """
  @spec check_rules_pinned(tuple()) :: :ok | {:error, {:rule_unpinned, [String.t()]}}
  def check_rules_pinned({:macro_def, _meta, rules}) do
    unpinned =
      rules
      |> Enum.filter(&(&1[:kind] == :syntax))
      |> Enum.filter(&(Map.get(&1, :examples, []) == []))
      |> Enum.map(& &1.keyword)

    case unpinned do
      [] -> :ok
      kws -> {:error, {:rule_unpinned, kws}}
    end
  end

  # Structural Diagnosis: one point per typed hole, per literal segment, AND
  # (for `:syntax` rules) the rule's own dispatch keyword — across all
  # syntax/literal rules, deduped and order-stable.
  #
  # NOTE: a `:syntax` rule's dispatch keyword lives in `rule.keyword`, NOT in
  # `rule.segments` (`segments` is only what follows it). Omitting it would mean
  # the single most common macro-use failure (typing the wrong keyword) could
  # never be required to have an `explain` clause — the plan's own headline
  # example (`syntax every <t: Duration> becomes …`) has NO literal `segments`.
  defp derive_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] in [:syntax, :literal, :fail]))
    |> Enum.flat_map(fn rule ->
      failure_points =
        case rule do
          %{kind: :fail, name: name} when is_binary(name) -> [{:failure, name}]
          _ -> []
        end

      keyword_points =
        case rule do
          %{kind: :syntax, keyword: kw} when is_binary(kw) -> [{:keyword, kw}]
          _ -> []
        end

      failure_points ++ keyword_points ++ Enum.map(Map.get(rule, :segments, []), &segment_point/1)
    end)
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
  end

  defp segment_point({:hole, %{kind: k}}), do: {:hole_kind, k}
  defp segment_point({:lit, w}), do: {:keyword, w}
  defp segment_point(_), do: nil

  # What the explain block covers, as a set of clause points.
  defp covered_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] == :explain))
    |> Enum.flat_map(& &1.clauses)
    |> Enum.map(& &1.point)
    |> MapSet.new()
  end

  # A `{:category, c}` clause covers a `{:hole_kind, c}` point; a `{:keyword, w}`
  # clause covers a `{:keyword, w}` point.
  defp covered?({:hole_kind, k}, covered), do: MapSet.member?(covered, {:category, k})
  defp covered?({:keyword, w}, covered), do: MapSet.member?(covered, {:keyword, w})
  defp covered?({:failure, name}, covered), do: MapSet.member?(covered, {:category, name})

  alias Cure.Compiler.Parser

  @doc """
  Check every `syntax` rule's `{:expansion, _}` example actually expands to its
  pinned result, up to α-renaming (design §5.1). `{:type, _}` pins are skipped
  (deferred). Returns `:ok` or `{:error, {:example_mismatch, mismatches}}`.
  """
  @spec check_examples(tuple()) :: :ok | {:error, {:example_mismatch, [map()]}}
  def check_examples({:macro_def, _meta, rules}) do
    mismatches =
      rules
      |> Enum.filter(&(&1[:kind] == :syntax))
      |> Enum.flat_map(fn rule ->
        for %{use_site: use_site, expected: {:expansion, expected}} <- Map.get(rule, :examples, []),
            actual = Parser.expand_example(rules, use_site),
            normalize(actual) != normalize(expected) do
          %{keyword: rule.keyword, expected: expected, actual: actual}
        end
      end)

    case mismatches do
      [] -> :ok
      ms -> {:error, {:example_mismatch, ms}}
    end
  end

  # α-normalise for example comparison: drop source positions, then collapse
  # `<fresh>` gensym suffixes (`x$0` → `x`) so a template binder and its pin
  # compare equal.
  #
  # A `:variable` node's meta is dropped ENTIRELY (not just line/col): it is
  # provenance about how the identifier was parsed (`scope: :local`,
  # `variant: true`, ...), not part of what the reference denotes. This
  # matters because a `<fresh Name>` marker in BINDER position parses to
  # `{:fresh_name, [line:, col:], name}` (no `scope` key -- that key is only
  # ever attached by the ordinary-identifier parse path) and `freshen/2`'s
  # `apply_freshening` reuses that meta verbatim when rewriting the marker to
  # `{:variable, meta, gensym}`. A hand-written pin's ordinary `h` always
  # carries `scope: :local`. Comparing full meta made every correctly-pinned
  # `<fresh>`-as-binder example spuriously mismatch; the only content that
  # participates in α-equivalence for a variable reference is its (degensym'd)
  # name.
  defp normalize({:variable, _meta, name}) when is_binary(name) do
    {:variable, [], degensym(name)}
  end

  defp normalize({t, meta, children}) when is_list(children) do
    {t, strip_pos(meta), Enum.map(children, &normalize/1)}
  end

  # A scalar-valued node (`:literal`'s {subtype, value} shape — `value` is a raw
  # integer/float/string/bool/atom/char, NOT a list of children) still carries
  # `:line`/`:col` in its meta that must be stripped, exactly like any other node.
  # Without this clause every `:literal` falls through to the catch-all UNCHANGED,
  # so its source position never gets stripped and check_examples rejects almost
  # every real macro example.
  defp normalize({t, meta, value}) when is_list(meta) do
    {t, strip_pos(meta), value}
  end

  defp normalize(other), do: other

  defp strip_pos(meta) when is_list(meta) do
    meta
    |> Enum.reject(fn
      {k, _} when k in [:line, :col] -> true
      _ -> false
    end)
    |> Enum.map(fn
      {k, v} -> {k, normalize_meta_value(v)}
      other -> other
    end)
  end

  defp strip_pos(meta), do: meta

  defp normalize_meta_value(v) when is_tuple(v), do: normalize(v)
  defp normalize_meta_value(v) when is_list(v), do: Enum.map(v, &normalize_meta_value/1)
  defp normalize_meta_value(v), do: v

  defp degensym(name) do
    case Regex.run(~r/^(.+)\$\d+$/, name) do
      [_, base] -> base
      _ -> name
    end
  end
end
