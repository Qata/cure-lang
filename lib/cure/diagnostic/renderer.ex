defmodule Cure.Diagnostic.Renderer do
  @moduledoc "Human and machine renderers for the shared diagnostic model."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Label, SourceRegistry, Span, Suggestion, TextEdit}

  @spec plain(Diagnostic.t(), SourceRegistry.t() | nil) :: String.t()
  def plain(%Diagnostic{} = diagnostic, registry \\ nil) do
    heading = heading(diagnostic)
    location = location_line(diagnostic.primary)
    excerpt = excerpt(diagnostic.primary, registry)
    secondary = Enum.map(diagnostic.secondary, &secondary_excerpt(&1, registry))
    message = diagnostic.message
    notes = Enum.map(diagnostic.notes, &"note: #{&1}")
    suggestions = Enum.map(diagnostic.suggestions, &"help: #{&1.message}")
    provenance = provenance_line(diagnostic.provenance)

    body =
      [message, location, excerpt, secondary, notes, suggestions, provenance]
      |> List.flatten()
      |> Enum.reject(&(&1 in [nil, ""]))
      |> Enum.join("\n\n")

    heading <> if(body == "", do: "", else: "\n\n" <> body)
  end

  defp heading(%Diagnostic{} = diagnostic) do
    label = diagnostic.title |> String.upcase()
    prefix = "-- #{label} [#{diagnostic.code}] "
    prefix <> String.duplicate("-", max(2, 72 - String.length(prefix)))
  end

  @spec terminal(Diagnostic.t(), SourceRegistry.t() | nil, keyword()) :: String.t()
  def terminal(%Diagnostic{} = diagnostic, registry \\ nil, opts \\ []) do
    rendered = plain(diagnostic, registry)
    if Keyword.get(opts, :color, false), do: colorize(rendered, diagnostic.severity), else: rendered
  end

  @spec to_map(Diagnostic.t()) :: map()
  def to_map(%Diagnostic{} = diagnostic) do
    %{
      "code" => diagnostic.code,
      "key" => Atom.to_string(diagnostic.key),
      "severity" => Atom.to_string(diagnostic.severity),
      "title" => diagnostic.title,
      "message" => diagnostic.message,
      "primary" => label_map(diagnostic.primary),
      "secondary" => Enum.map(diagnostic.secondary, &label_map/1),
      "notes" => diagnostic.notes,
      "suggestions" => Enum.map(diagnostic.suggestions, &suggestion_map/1),
      "provenance" => Enum.map(diagnostic.provenance, &provenance_map/1),
      "payload" => stringify_keys(diagnostic.payload)
    }
  end

  @spec json(Diagnostic.t()) :: String.t()
  def json(%Diagnostic{} = diagnostic), do: Jason.encode!(to_map(diagnostic))

  @doc "Project a Cure diagnostic into Elixir's compiler diagnostic envelope."
  @spec code_diagnostic(Diagnostic.t()) :: Code.diagnostic(Diagnostic.severity())
  def code_diagnostic(%Diagnostic{} = diagnostic) do
    span = primary_span(diagnostic)

    %{
      severity: diagnostic.severity,
      message: "[#{diagnostic.code}] #{diagnostic.title}\n\n#{diagnostic.message}",
      source: authored_source_path(diagnostic) || path(span),
      file: path(span),
      position: start_position(span),
      span: end_position(span),
      stacktrace: Map.get(diagnostic.payload, :stacktrace, []),
      details: diagnostic
    }
  end

  @doc "Project a Cure diagnostic into the standard Mix compiler structure."
  @spec mix_diagnostic(Diagnostic.t()) :: Mix.Task.Compiler.Diagnostic.t()
  def mix_diagnostic(%Diagnostic{} = diagnostic) do
    diagnostic
    |> code_diagnostic()
    |> Map.put(:compiler_name, "Cure")
    |> then(&struct!(Mix.Task.Compiler.Diagnostic, &1))
  end

  @doc "Recover the lossless Cure value carried by a host diagnostic."
  @spec from_host_diagnostic(map()) :: {:ok, Diagnostic.t()} | :error
  def from_host_diagnostic(%{details: %Diagnostic{} = diagnostic}), do: {:ok, diagnostic}
  def from_host_diagnostic(_diagnostic), do: :error

  @spec lsp(Diagnostic.t(), SourceRegistry.t() | nil, :utf8 | :utf16 | :utf32) :: map()
  def lsp(%Diagnostic{} = diagnostic, registry \\ nil, encoding \\ :utf16) do
    %{
      "range" => lsp_range(diagnostic.primary, registry, encoding),
      "severity" => lsp_severity(diagnostic.severity),
      "code" => diagnostic.code,
      "source" => "cure",
      "message" => diagnostic.title <> "\n\n" <> diagnostic.message,
      "relatedInformation" => Enum.map(diagnostic.secondary, &related_information(&1, registry, encoding)),
      "data" => %{
        "key" => Atom.to_string(diagnostic.key),
        "suggestions" => Enum.map(diagnostic.suggestions, &lsp_suggestion_map(&1, registry, encoding)),
        "provenance" => Enum.map(diagnostic.provenance, &provenance_map/1),
        "payload" => stringify_keys(diagnostic.payload)
      }
    }
  end

  defp location_line(nil), do: nil

  defp location_line(%Label{span: span}) do
    "at #{span.path || inspect(span.source_id)}:#{span.start_line}:#{span.start_column}"
  end

  defp excerpt(nil, _registry), do: nil
  defp excerpt(_label, nil), do: nil

  defp excerpt(%Label{span: %Span{} = span, message: message} = label, %SourceRegistry{} = registry) do
    lines = span.start_line..span.end_line

    rendered =
      Enum.map(lines, fn line_number ->
        case SourceRegistry.line(registry, span, line_number) do
          {:ok, source_line} -> render_excerpt_line(span, line_number, source_line, message, label.style)
          :error -> nil
        end
      end)
      |> Enum.reject(&is_nil/1)

    case rendered do
      [] -> nil
      lines -> Enum.join(lines, "\n")
    end
  end

  defp render_excerpt_line(span, line_number, source_line, message, style) do
    start_column = if line_number == span.start_line, do: span.start_column, else: 1

    end_column =
      cond do
        line_number == span.end_line -> span.end_column
        true -> String.length(source_line) + 1
      end

    visual_start = visual_column(source_line, start_column)
    visual_end = visual_column(source_line, end_column)
    width = max(visual_end - visual_start, 1)
    marker_character = if style == :secondary, do: "-", else: "^"
    marker = String.duplicate(" ", visual_start - 1) <> String.duplicate(marker_character, width)
    suffix = if line_number == span.end_line and message, do: " " <> message, else: ""
    gutter = String.length(Integer.to_string(line_number))
    "#{line_number} | #{expand_tabs(source_line)}\n#{String.duplicate(" ", gutter)} | #{marker}#{suffix}"
  end

  @tab_width 4

  defp visual_column(line, scalar_column) do
    line
    |> String.codepoints()
    |> Enum.take(scalar_column - 1)
    |> Enum.reduce(1, fn
      "\t", column -> column + (@tab_width - rem(column - 1, @tab_width))
      _codepoint, column -> column + 1
    end)
  end

  defp expand_tabs(line) do
    {parts, _column} =
      line
      |> String.codepoints()
      |> Enum.map_reduce(1, fn
        "\t", column ->
          width = @tab_width - rem(column - 1, @tab_width)
          {String.duplicate(" ", width), column + width}

        codepoint, column ->
          {codepoint, column + 1}
      end)

    IO.iodata_to_binary(parts)
  end

  defp secondary_excerpt(_label, nil), do: nil

  defp secondary_excerpt(%Label{} = label, %SourceRegistry{} = registry) do
    case excerpt(label, registry) do
      nil ->
        nil

      rendered ->
        "also at #{label.span.path || inspect(label.span.source_id)}:#{label.span.start_line}:#{label.span.start_column}\n" <>
          rendered
    end
  end

  defp provenance_line([]), do: nil

  defp provenance_line(frames) do
    chain = Enum.map_join(frames, " -> ", &to_string(&1.name))
    "expansion: " <> chain
  end

  defp label_map(nil), do: nil

  defp label_map(%Label{span: span, message: message, style: style}) do
    %{"span" => span_map(span), "message" => message, "style" => Atom.to_string(style)}
  end

  defp span_map(%Span{} = span) do
    span
    |> Map.from_struct()
    |> stringify_keys()
  end

  defp suggestion_map(%Suggestion{} = suggestion) do
    %{
      "message" => suggestion.message,
      "applicability" => Atom.to_string(suggestion.applicability),
      "edits" => Enum.map(suggestion.edits, &edit_map/1)
    }
  end

  defp lsp_suggestion_map(%Suggestion{} = suggestion, registry, encoding) do
    %{
      "message" => suggestion.message,
      "applicability" => Atom.to_string(suggestion.applicability),
      "edits" =>
        Enum.map(suggestion.edits, fn %TextEdit{span: span, replacement: replacement} ->
          %{
            "uri" => path_to_uri(span.path),
            "range" => lsp_range(%Label{span: span, style: :primary}, registry, encoding),
            "newText" => replacement
          }
        end)
    }
  end

  defp edit_map(%TextEdit{span: span, replacement: replacement}) do
    %{"span" => span_map(span), "replacement" => replacement}
  end

  defp provenance_map(frame) do
    %{
      "kind" => Atom.to_string(frame.kind),
      "name" => to_string(frame.name),
      "invocation" => optional_span(frame.invocation),
      "definition" => optional_span(frame.definition),
      "generated" => optional_span(frame.generated),
      "parent" => frame.parent
    }
  end

  defp optional_span(%Span{} = span), do: span_map(span)
  defp optional_span(other), do: other

  defp lsp_range(nil, _registry, _encoding),
    do: %{"start" => %{"line" => 0, "character" => 0}, "end" => %{"line" => 0, "character" => 0}}

  defp lsp_range(%Label{span: span}, %SourceRegistry{} = registry, encoding) do
    with {:ok, start_position} <- SourceRegistry.lsp_position(registry, span, :start, encoding),
         {:ok, end_position} <- SourceRegistry.lsp_position(registry, span, :end, encoding) do
      %{"start" => start_position, "end" => end_position}
    else
      _ -> lsp_range(%Label{span: span, style: :primary}, nil, encoding)
    end
  end

  defp lsp_range(%Label{span: span}, nil, _encoding) do
    %{
      "start" => %{"line" => span.start_line - 1, "character" => span.start_column - 1},
      "end" => %{"line" => span.end_line - 1, "character" => span.end_column - 1}
    }
  end

  defp related_information(%Label{span: span, message: message} = label, registry, encoding) do
    %{
      "location" => %{"uri" => path_to_uri(span.path), "range" => lsp_range(label, registry, encoding)},
      "message" => message || "related source"
    }
  end

  defp primary_span(%Diagnostic{primary: %Label{span: span}}), do: span
  defp primary_span(_diagnostic), do: nil

  defp path(%Span{path: path}), do: path
  defp path(nil), do: nil

  defp start_position(%Span{} = span), do: {span.start_line, span.start_column}
  defp start_position(nil), do: 0

  defp end_position(%Span{} = span), do: {span.end_line, span.end_column}
  defp end_position(nil), do: nil

  defp authored_source_path(%Diagnostic{provenance: provenance}) do
    provenance
    |> Enum.reverse()
    |> Enum.find_value(fn frame ->
      case frame.invocation do
        %Span{path: path} -> path
        _ -> nil
      end
    end)
  end

  defp path_to_uri(nil), do: ""
  defp path_to_uri("file://" <> _ = uri), do: uri
  defp path_to_uri(path), do: "file://" <> Path.expand(path)

  defp lsp_severity(:error), do: 1
  defp lsp_severity(:warning), do: 2
  defp lsp_severity(:information), do: 3
  defp lsp_severity(:hint), do: 4

  defp stringify_keys(map) when is_map(map) do
    Map.new(map, fn {key, value} -> {to_string(key), stringify_keys(value)} end)
  end

  defp stringify_keys(list) when is_list(list), do: Enum.map(list, &stringify_keys/1)
  defp stringify_keys(value) when is_atom(value), do: Atom.to_string(value)
  defp stringify_keys(value), do: value

  defp colorize(rendered, severity) do
    primary_color = if severity == :warning, do: IO.ANSI.yellow(), else: IO.ANSI.red()
    reset = IO.ANSI.reset()

    rendered
    |> String.split("\n")
    |> Enum.with_index()
    |> Enum.map_join("\n", fn
      {line, 0} -> IO.ANSI.cyan() <> line <> reset
      {line, _index} -> color_marker_line(line, primary_color, reset)
    end)
  end

  defp color_marker_line(line, primary_color, reset) do
    Regex.replace(~r/^(\s*\|\s*\s*)(\^+)(.*)$/u, line, fn _, prefix, marker, suffix ->
      prefix <> primary_color <> marker <> reset <> suffix
    end)
    |> then(fn colored ->
      Regex.replace(~r/^(\s*\|\s*\s*)(-+)(.*)$/u, colored, fn _, prefix, marker, suffix ->
        prefix <> IO.ANSI.cyan() <> marker <> reset <> suffix
      end)
    end)
  end
end
