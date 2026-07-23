defmodule Cure.Diagnostic.Adapter.Macro do
  @moduledoc """
  Converts authored macro-family and expansion failures.

  Generated implementation details remain in payloads and provenance; primary
  labels point at authored macro syntax whenever a source span is available.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion, TextEdit}
  alias Cure.Diagnostic.Suggest

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:unknown_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :unknown_syntax_family_field,
      severity: :error,
      title: "Unknown syntax-family field",
      body: Doc.paragraph("`#{details.field}` is not a field of the `#{details.family}` syntax family."),
      primary:
        label(
          span,
          :primary,
          "this field is not declared by the family"
        ),
      suggestions: syntax_family_field_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:missing_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :missing_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is missing",
      body: Doc.paragraph("The `#{details.family}` syntax family requires a `#{details.field}` section here."),
      primary: label(span, :primary, "add `#{details.field}` here"),
      suggestions: [
        %Suggestion{
          message: "Add a `#{details.field} ...` section to this family body",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:unknown_macro_obligation_capture, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :unknown_macro_obligation_capture,
      severity: :error,
      title: "Unknown macro capture",
      body:
        Doc.paragraph(
          "The `#{details.interface}` obligation refers to `#{details.capture}`, but this rule declares no capture with that name."
        ),
      primary:
        label(
          span,
          :primary,
          "this capture is not declared by the rule"
        ),
      suggestions: macro_capture_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:unit_type_reserved, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case label(
             Map.get(details, :unit_span),
             :secondary,
             "this spelling denotes the built-in `Unit` type"
           ) do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E092",
      key: :unit_type_reserved,
      severity: :error,
      title: "Unit syntax cannot define another type",
      body: Doc.paragraph("`()` has exactly one type, `Unit`, so it cannot define the new type `#{details.name}`."),
      primary:
        label(
          span,
          :primary,
          "this declaration must not reuse `Unit` syntax"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Give `#{details.name}` its own constructor, or rename the type to `Unit`",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:duplicate_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case label(
             Map.get(details, :first_span),
             :secondary,
             "the field was first supplied here"
           ) do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E092",
      key: :duplicate_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is duplicated",
      body: Doc.paragraph("The `#{details.field}` field may be supplied only once in this family body."),
      primary:
        label(
          span,
          :primary,
          "this second `#{details.field}` field is redundant"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Keep one `#{details.field}` section",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error(error, _opts),
    do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp syntax_family_field_suggestions(
         %{field: field, valid_fields: fields},
         %Span{} = span
       )
       when is_list(fields),
       do:
         ranked_repair(
           field,
           fields,
           span,
           fn candidate -> "Replace it with `#{candidate}`" end,
           fn candidates ->
             "Use one of: #{Enum.map_join(candidates, ", ", fn field -> "`#{field}`" end)}"
           end
         )

  defp syntax_family_field_suggestions(_details, _span), do: []

  defp macro_capture_suggestions(
         %{capture: capture, available_captures: captures},
         %Span{} = span
       )
       when is_list(captures),
       do:
         ranked_repair(
           capture,
           captures,
           span,
           fn candidate ->
             "Replace it with the declared capture `#{candidate}`"
           end,
           fn candidates ->
             "Refer to one of this rule's captures: #{Enum.map_join(candidates, ", ", fn capture -> "`#{capture}`" end)}"
           end
         )

  defp macro_capture_suggestions(_details, _span), do: []

  defp ranked_repair(spelling, candidates, span, unique_message, fallback_message) do
    spelling = to_string(spelling)

    ranked =
      candidates
      |> Enum.map(&{to_string(&1), Suggest.distance(spelling, to_string(&1))})
      |> Enum.sort_by(fn {candidate, distance} ->
        {distance, String.downcase(candidate), candidate}
      end)

    case ranked do
      [{candidate, distance}, {_other, next_distance} | _]
      when distance <= 2 and distance < next_distance ->
        [replacement(candidate, span, unique_message)]

      [{candidate, distance}] when distance <= 2 ->
        [replacement(candidate, span, unique_message)]

      _ ->
        [
          %Suggestion{
            message: fallback_message.(candidates),
            applicability: :manual
          }
        ]
    end
  end

  defp replacement(candidate, span, message) do
    %Suggestion{
      message: message.(candidate),
      applicability: :machine_applicable,
      edits: [%TextEdit{span: span, replacement: candidate}]
    }
  end

  defp label(%Span{} = span, style, message),
    do: %Label{span: span, style: style, message: message}

  defp label(_span, _style, _message), do: nil
end
