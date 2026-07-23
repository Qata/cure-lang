defmodule Cure.Diagnostic.Adapter.Syntax do
  @moduledoc """
  Converts contextual surface-syntax failures.

  This family owns token and authored-shape diagnostics. It does not accept a
  generic ordinary-error fallback: every producer branch is explicit.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion, TextEdit}
  alias Cure.Diagnostic.Suggest

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:graded_let_requires_variable, details}, opts)
      when is_map(details) do
    pattern_span = Map.get(details, :pattern_span) || Keyword.get(opts, :span)
    grade_span = Map.get(details, :grade_span)

    secondary =
      case label(grade_span, :secondary, "this grade applies to the binding") do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E093",
      key: :graded_let_requires_variable,
      severity: :error,
      title: "Graded binding needs a variable",
      body:
        Doc.paragraph(
          "A `#{details.grade}` grade controls one Core binder, but this pattern introduces multiple or destructured bindings."
        ),
      primary:
        label(
          pattern_span,
          :primary,
          "this pattern is not a single variable binding"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Bind the value to one graded variable, then destructure it in a separate `let`",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:unknown_grade, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)
    supported = Map.get(details, :supported, [:erased, :linear, :affine])
    supported_text = Enum.map_join(supported, ", ", &"`:#{&1}`")

    Diagnostic.new(
      code: "E093",
      key: :unknown_grade,
      severity: :error,
      title: "Unknown relevance grade",
      body: Doc.paragraph("`:#{details.grade}` is not a relevance grade. Cure supports #{supported_text}."),
      primary: label(span, :primary, "this grade is not defined"),
      suggestions: grade_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:grade_requires_type, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :grade_requires_type,
      severity: :error,
      title: "Graded parameter needs a type",
      body:
        Doc.paragraph(
          "The `:#{details.grade}` grade on `#{details.name}` controls how a value may be used, but no value type follows it."
        ),
      primary:
        label(
          span,
          :primary,
          "add the parameter type after this grade"
        ),
      suggestions: [
        %Suggestion{
          message: "Write `#{details.name} :#{details.grade} TypeName`",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error(error, _opts),
    do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp grade_suggestions(
         %{grade: grade, supported: supported},
         %Span{} = span
       ) do
    spelling = to_string(grade)

    ranked =
      supported
      |> Enum.map(&{&1, Suggest.distance(spelling, to_string(&1))})
      |> Enum.sort_by(fn {candidate, distance} ->
        {distance, to_string(candidate)}
      end)

    case ranked do
      [{candidate, distance}, {_other, next_distance} | _]
      when distance <= 2 and distance < next_distance ->
        [grade_edit(candidate, span)]

      [{candidate, distance}] when distance <= 2 ->
        [grade_edit(candidate, span)]

      _ ->
        [
          %Suggestion{
            message: "Use `:erased`, `:linear`, `:affine`, or omit the grade for unrestricted use",
            applicability: :manual
          }
        ]
    end
  end

  defp grade_suggestions(_details, _span), do: []

  defp grade_edit(candidate, span) do
    %Suggestion{
      message: "Replace it with `:#{candidate}`",
      applicability: :machine_applicable,
      edits: [%TextEdit{span: span, replacement: ":#{candidate}"}]
    }
  end

  defp label(%Span{} = span, style, message),
    do: %Label{span: span, style: style, message: message}

  defp label(_span, _style, _message), do: nil
end
