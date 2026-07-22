defmodule Cure.MetaAST.Metadata do
  @moduledoc "The single semantic and source-information contract for MetaAST metadata."

  alias Cure.MetaAST.SourceInfo

  @source_keys [
    :source_info,
    :span,
    :construct_span,
    :name_span,
    :callee_span,
    :operator_span,
    :operand_spans,
    :argument_spans,
    :arg_label_spans,
    :annotation_span,
    :body_span,
    :condition_span,
    :then_span,
    :else_span,
    :pattern_span,
    :guard_span,
    :branch_spans,
    :field_spans,
    :subject_span,
    :case_span,
    :hypothesis_spans,
    :constructor_declarations,
    :constructor_span,
    :opener_span,
    :closer_span,
    :provenance,
    :source_provenance,
    :expansion_provenance,
    :line,
    :col,
    :column
  ]

  @spec source_info(keyword()) :: SourceInfo.t() | nil
  def source_info(meta) when is_list(meta) do
    case Keyword.get(meta, :source_info) do
      %SourceInfo{} = info -> info
      _ -> legacy_source_info(meta)
    end
  end

  def source_info(_), do: nil

  @spec put_source_info(keyword(), SourceInfo.t()) :: keyword()
  def put_source_info(meta, %SourceInfo{} = info) when is_list(meta) do
    meta
    |> Keyword.drop(@source_keys)
    |> Keyword.put(:source_info, info)
  end

  @spec drop_source_info(keyword()) :: keyword()
  def drop_source_info(meta) when is_list(meta), do: Keyword.drop(meta, @source_keys)
  def drop_source_info(meta), do: meta

  @spec strip_diagnostics(term()) :: term()
  def strip_diagnostics({tag, meta, children}) when is_atom(tag) and is_list(meta) do
    {tag, strip_metadata(meta), strip_diagnostics(children)}
  end

  def strip_diagnostics(list) when is_list(list), do: Enum.map(list, &strip_diagnostics/1)

  def strip_diagnostics(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.map(&strip_diagnostics/1) |> List.to_tuple()
  end

  def strip_diagnostics(map) when is_map(map) and not is_struct(map) do
    Map.new(map, fn {key, value} -> {strip_diagnostics(key), strip_diagnostics(value)} end)
  end

  def strip_diagnostics(%_{} = struct), do: struct
  def strip_diagnostics(other), do: other

  @spec semantic_equal?(term(), term()) :: boolean()
  def semantic_equal?(left, right), do: strip_diagnostics(left) == strip_diagnostics(right)

  @spec semantic_key(term()) :: term()
  def semantic_key(ast), do: strip_diagnostics(ast)

  @doc false
  def source_keys, do: @source_keys

  @doc "Whether a metadata key belongs to the diagnostic/source contract."
  @spec diagnostic_key?(term()) :: boolean()
  def diagnostic_key?(key), do: key in @source_keys

  defp strip_metadata(meta) do
    meta
    |> drop_source_info()
    |> Enum.map(fn {key, value} -> {key, strip_diagnostics(value)} end)
  end

  defp legacy_source_info(meta) do
    fields = %{
      whole: Keyword.get(meta, :construct_span, Keyword.get(meta, :span)),
      name: Keyword.get(meta, :name_span),
      callee: Keyword.get(meta, :callee_span),
      operator: Keyword.get(meta, :operator_span),
      operands: Keyword.get(meta, :operand_spans, []),
      arguments: Keyword.get(meta, :argument_spans, []),
      argument_labels: Keyword.get(meta, :arg_label_spans, []),
      annotation: Keyword.get(meta, :annotation_span),
      body: Keyword.get(meta, :body_span),
      condition: Keyword.get(meta, :condition_span),
      then_branch: Keyword.get(meta, :then_span),
      else_branch: Keyword.get(meta, :else_span),
      pattern: Keyword.get(meta, :pattern_span),
      guard: Keyword.get(meta, :guard_span),
      branches: Keyword.get(meta, :branch_spans, []),
      fields: Keyword.get(meta, :field_spans, %{}),
      opener: Keyword.get(meta, :opener_span),
      closer: Keyword.get(meta, :closer_span),
      provenance: Keyword.get(meta, :provenance, [])
    }

    if Enum.any?(Map.values(fields), &present_source_value?/1), do: struct(SourceInfo, fields), else: nil
  end

  defp present_source_value?(value) when value in [nil, [], %{}], do: false
  defp present_source_value?(_), do: true
end
