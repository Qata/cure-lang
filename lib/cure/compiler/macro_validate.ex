# lib/cure/compiler/macro_validate.ex
defmodule Cure.Compiler.MacroValidate do
  @moduledoc """
  Frontend validation of `macro` definitions against the self-proving
  obligations (design 2026-07-11 §3). TCB delta zero — pure analysis over the
  parsed `{:macro_def, …}` AST, upstream of the elaborator.
  """

  @type point :: {:hole_kind, String.t()} | {:keyword, String.t()}

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
    |> Enum.filter(&(&1[:kind] in [:syntax, :literal]))
    |> Enum.flat_map(fn rule ->
      keyword_points =
        case rule do
          %{kind: :syntax, keyword: kw} when is_binary(kw) -> [{:keyword, kw}]
          _ -> []
        end

      keyword_points ++ Enum.map(rule.segments, &segment_point/1)
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
end
