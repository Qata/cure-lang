defmodule Cure.Compiler.SourceSpans do
  @moduledoc "Attach authored token ranges to parser AST metadata without changing semantic identity."

  alias Cure.Compiler.Token
  alias Cure.Diagnostic.Span
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @spec attach(term(), [Token.t()]) :: term()
  def attach(ast, tokens) do
    tokens = tokens |> flatten_tokens() |> Enum.filter(&match?(%Token{span: %Span{}}, &1))
    context = index_tokens(tokens)
    {ast, _span} = attach_term(ast, context)
    ast
  end

  @doc "Remove source/provenance metadata before a semantic comparison."
  @spec strip_diagnostic_meta(term()) :: term()
  def strip_diagnostic_meta(ast), do: Metadata.strip_diagnostics(ast)

  defp attach_term({tag, meta, payload}, context) when is_atom(tag) and is_list(meta) do
    # Declarations keep annotations, parameters, guards, and constraints in
    # metadata rather than their payload. Descend through those authored syntax
    # values before attaching this node's own range; otherwise diagnostics can
    # locate a function body but not the type that was written on its header.
    {meta, _metadata_span} = attach_term(meta, context)
    {payload, child_spans} = attach_payload(payload, context)
    own = metadata_span(meta, context.by_position)
    span = complete_span(own, child_spans)

    {meta, span} =
      case own do
        %Span{} ->
          span = expand_construct(tag, meta, span, context)
          {attach_metadata(meta, tag, span, context, direct_child_spans(payload)), span}

        nil ->
          {meta, span}
      end

    {{tag, meta, payload}, span}
  end

  defp attach_term(list, context) when is_list(list) do
    {items, spans} =
      Enum.map_reduce(list, [], fn item, spans ->
        {item, span} = attach_term(item, context)
        {item, add_span(spans, span)}
      end)

    {items, complete_span(nil, spans)}
  end

  defp attach_term(tuple, context) when is_tuple(tuple) do
    {items, spans} =
      tuple
      |> Tuple.to_list()
      |> Enum.map_reduce([], fn item, spans ->
        {item, span} = attach_term(item, context)
        {item, add_span(spans, span)}
      end)

    {List.to_tuple(items), complete_span(nil, spans)}
  end

  defp attach_term(other, _context), do: {other, nil}

  defp attach_payload(payload, context) do
    {payload, span} = attach_term(payload, context)
    {payload, add_span([], span)}
  end

  defp metadata_span(meta, by_position) do
    case Metadata.source_info(meta) do
      %SourceInfo{whole: %Span{} = span} ->
        span

      _ ->
        metadata_span_from_position(meta, by_position)
    end
  end

  defp metadata_span_from_position(meta, by_position) do
    case {Keyword.get(meta, :line), Keyword.get(meta, :col, Keyword.get(meta, :column))} do
      {line, column} when is_integer(line) and is_integer(column) ->
        case Map.get(by_position, {line, column}) do
          %Token{span: %Span{} = span} -> span
          _ -> nil
        end

      _ ->
        Keyword.get(meta, :span)
    end
  end

  defp complete_span(nil, []), do: nil
  defp complete_span(%Span{} = own, []), do: own
  defp complete_span(nil, spans), do: Enum.reduce(spans, &merge_spans/2)
  defp complete_span(%Span{} = own, spans), do: Enum.reduce(spans, own, &merge_spans/2)

  defp merge_spans(%Span{source_id: source_id} = right, %Span{source_id: source_id} = left) do
    start = if left.start_byte <= right.start_byte, do: left, else: right
    ending = if left.end_byte >= right.end_byte, do: left, else: right

    %Span{
      start
      | end_byte: ending.end_byte,
        end_line: ending.end_line,
        end_column: ending.end_column
    }
  end

  defp merge_spans(_right, left), do: left

  defp attach_metadata(meta, tag, span, context, child_spans) do
    info = Metadata.source_info(meta) || %SourceInfo{}
    info = put_if_missing(info, :whole, span)

    info =
      case Map.get(context.opening_delimiters, {span.source_id, span.start_byte}) do
        %Span{} = opener ->
          closer = Map.get(context.closing_delimiters, {span.source_id, span.start_byte})
          info |> put_if_missing(:opener, opener) |> put_if_missing(:closer, closer)

        _ ->
          info
      end

    info =
      case operator_span(meta, context.by_position) do
        %Span{} = operator -> put_if_missing(info, :operator, operator)
        nil -> info
      end

    info = role_spans(info, tag, meta, child_spans)

    case name_span(meta, span, context) do
      nil ->
        put_source_info(meta, info)

      name_span when tag in [:function_call, :remote_call] ->
        info = info |> put_if_missing(:name, name_span) |> put_if_missing(:callee, name_span)
        put_source_info(meta, info)

      name_span ->
        put_source_info(meta, put_if_missing(info, :name, name_span))
    end
  end

  defp role_spans(info, :function_call, _meta, child_spans),
    do: put_if_missing(info, :arguments, child_spans)

  defp role_spans(info, :remote_call, _meta, child_spans),
    do: put_if_missing(info, :arguments, child_spans)

  defp role_spans(info, :binary_op, _meta, child_spans),
    do: put_if_missing(info, :operands, child_spans)

  defp role_spans(info, :unary_op, _meta, child_spans),
    do: put_if_missing(info, :operands, child_spans)

  defp role_spans(info, :function_def, meta, child_spans) do
    info
    |> maybe_role(:annotation, metadata_value_span(meta, :return_type))
    |> maybe_role(:guard, metadata_value_span(meta, :guards))
    |> maybe_role(:body, List.last(child_spans))
  end

  defp role_spans(info, :match_arm, meta, child_spans) do
    info
    |> maybe_role(:pattern, metadata_value_span(meta, :pattern))
    |> maybe_role(:guard, metadata_value_span(meta, :guard))
    |> maybe_role(:body, List.last(child_spans))
  end

  defp role_spans(info, _tag, _meta, _child_spans), do: info

  defp metadata_value_span(meta, key) do
    case Keyword.get(meta, key) do
      value when is_tuple(value) -> Metadata.source_info(elem(value, 1)) |> source_whole()
      values when is_list(values) -> Enum.find_value(values, &metadata_value_span_value/1)
      _ -> nil
    end
  end

  defp metadata_value_span_value(value) when is_tuple(value),
    do: Metadata.source_info(elem(value, 1)) |> source_whole()

  defp metadata_value_span_value(_), do: nil

  defp source_whole(%SourceInfo{whole: span}), do: span
  defp source_whole(_), do: nil

  defp maybe_role(info, _field, nil), do: info
  defp maybe_role(info, field, span), do: put_if_missing(info, field, span)

  defp put_if_missing(info, _field, value) when value in [nil, []], do: info

  defp put_if_missing(info, field, value),
    do: if(Map.get(info, field) in [nil, []], do: Map.put(info, field, value), else: info)

  defp direct_child_spans(payload) when is_list(payload) do
    Enum.flat_map(payload, fn
      {_, meta, _} when is_list(meta) ->
        case Metadata.source_info(meta) do
          %SourceInfo{whole: %Span{} = span} -> [span]
          _ -> []
        end

      _ ->
        []
    end)
  end

  defp direct_child_spans(_), do: []

  defp put_source_info(meta, %SourceInfo{} = info) do
    # Keep the parser's existing line/column fields available during the
    # compatibility window; all range and provenance roles have one canonical
    # owner under :source_info.
    meta
    |> Keyword.drop(Metadata.source_keys() -- [:line, :col, :column])
    |> Keyword.put(:source_info, info)
  end

  defp expand_construct(:function_call, meta, %Span{} = span, context) do
    name_span = name_span(meta, span, context)
    start_span = name_span || span

    # Expression calls historically carry the opening-paren location, while
    # type applications carry the type-name location. Support both without a
    # width guess: locate the authored `(` immediately after the callee and use
    # the lexer-derived matching `)` range.
    opening_start =
      case Map.get(context.opening_parens, {start_span.source_id, start_span.end_byte}) do
        %Span{} = opening -> opening.start_byte
        nil -> span.start_byte
      end

    case Map.get(context.closing_parens, {span.source_id, opening_start}) do
      %Span{} = closing_span -> merge_spans(closing_span, start_span)
      nil -> merge_spans(span, start_span)
    end
  end

  defp expand_construct(_tag, _meta, %Span{} = span, context) do
    case Map.get(context.closing_delimiters, {span.source_id, span.start_byte}) do
      %Span{} = closing -> merge_spans(closing, span)
      nil -> span
    end
  end

  defp expand_construct(_tag, _meta, span, _context), do: span

  defp operator_span(meta, by_position) do
    operator = Keyword.get(meta, :operator)
    line = Keyword.get(meta, :line)
    column = Keyword.get(meta, :col, Keyword.get(meta, :column))

    if not is_nil(operator) and is_integer(line) and is_integer(column) do
      case Map.get(by_position, {line, column}) do
        %Token{span: %Span{} = span} = token ->
          if token_spelling(token) == to_string(operator), do: span

        _ ->
          nil
      end
    end
  end

  defp name_span(meta, span, context) do
    name = Keyword.get(meta, :name)

    if is_binary(name) or is_atom(name) do
      spelling = to_string(name)

      context.by_name
      |> Map.get({span.source_id, span.start_line, spelling}, [])
      |> Enum.reverse()
      |> Enum.filter(fn %Token{span: token_span} ->
        token_span.start_byte >= span.start_byte and token_span.end_byte <= span.end_byte
      end)
      |> Enum.find_value(fn token -> if token_spelling(token) == spelling, do: token.span end)
      |> case do
        nil ->
          context.by_name
          |> Map.get({span.source_id, span.start_line, spelling}, [])
          |> Enum.filter(fn %Token{span: token_span} -> token_span.end_byte <= span.start_byte end)
          |> Enum.reverse()
          |> Enum.find_value(fn token -> if token_spelling(token) == spelling, do: token.span end)

        found ->
          found
      end
    end
  end

  defp token_spelling(%Token{value: value}) when is_binary(value), do: value
  defp token_spelling(%Token{value: value}) when is_atom(value), do: Atom.to_string(value)
  defp token_spelling(_token), do: nil

  defp index_tokens(tokens) do
    %{
      by_position: Map.new(tokens, fn token -> {{token.line, token.col}, token} end),
      by_name:
        Enum.reduce(tokens, %{}, fn token, index ->
          case token_spelling(token) do
            nil -> index
            spelling -> Map.update(index, {token.span.source_id, token.line, spelling}, [token], &[token | &1])
          end
        end),
      opening_parens: opening_parens(tokens),
      closing_parens: closing_parens(tokens),
      opening_delimiters: opening_delimiters(tokens),
      closing_delimiters: closing_delimiters(tokens)
    }
  end

  defp opening_parens(tokens) do
    Enum.reduce(tokens, %{}, fn
      %Token{type: :lparen, span: %Span{} = span}, openings ->
        Map.put(openings, {span.source_id, span.start_byte}, span)

      _token, openings ->
        openings
    end)
  end

  defp closing_parens(tokens) do
    {pairs, _stacks} =
      Enum.reduce(tokens, {%{}, %{}}, fn
        %Token{type: :lparen, span: span}, {pairs, stacks} ->
          key = span.source_id
          {pairs, Map.update(stacks, key, [span], &[span | &1])}

        %Token{type: :rparen, span: closing}, {pairs, stacks} ->
          key = closing.source_id

          case Map.get(stacks, key, []) do
            [opening | rest] ->
              {Map.put(pairs, {key, opening.start_byte}, closing), Map.put(stacks, key, rest)}

            [] ->
              {pairs, stacks}
          end

        _token, acc ->
          acc
      end)

    pairs
  end

  defp closing_delimiters(tokens) do
    pairs = [
      {:lparen, :rparen},
      {:lbracket, :rbracket},
      {:lbrace, :rbrace},
      {:tuple_open, :rbracket},
      {:map_open, :rbrace}
    ]

    {pairs, _stacks} =
      Enum.reduce(tokens, {%{}, %{}}, fn
        %Token{type: opening, span: %Span{} = span}, {pairs_by_position, stacks}
        when opening in [:lparen, :lbracket, :lbrace, :tuple_open, :map_open] ->
          key = span.source_id
          {pairs_by_position, Map.update(stacks, key, [{opening, span}], &[{opening, span} | &1])}

        %Token{type: closing, span: %Span{} = closing_span}, {pairs_by_position, stacks}
        when closing in [:rparen, :rbracket, :rbrace] ->
          key = closing_span.source_id

          case Map.get(stacks, key, []) do
            [{opening, opening_span} | rest] ->
              if {opening, closing} in pairs do
                {Map.put(pairs_by_position, {key, opening_span.start_byte}, closing_span), Map.put(stacks, key, rest)}
              else
                {pairs_by_position, stacks}
              end

            _ ->
              {pairs_by_position, stacks}
          end

        _token, acc ->
          acc
      end)

    pairs
  end

  defp opening_delimiters(tokens) do
    Enum.reduce(tokens, %{}, fn
      %Token{type: type, span: %Span{} = span}, openings
      when type in [:lparen, :lbracket, :lbrace, :tuple_open, :map_open] ->
        Map.put(openings, {span.source_id, span.start_byte}, span)

      _token, openings ->
        openings
    end)
  end

  defp add_span(spans, %Span{} = span), do: [span | spans]
  defp add_span(spans, _span), do: spans

  defp flatten_tokens(tokens) do
    Enum.flat_map(tokens, fn token ->
      nested =
        case token.value do
          parts when is_list(parts) ->
            Enum.flat_map(parts, fn
              {:expr, expression_tokens} -> flatten_tokens(expression_tokens)
              _ -> []
            end)

          _ ->
            []
        end

      [token | nested]
    end)
  end
end
