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

  def from_error(
        {:source_context, {:forced_pattern_not_in_pattern, _meta}, context},
        opts
      )
      when is_map(context),
      do: pattern_only_syntax(:forced_pattern, context, opts)

  def from_error(
        {:source_context, {:named_implicit_not_in_pattern, _meta}, context},
        opts
      )
      when is_map(context),
      do: pattern_only_syntax(:named_implicit_pattern, context, opts)

  def from_error({:forced_pattern_not_in_pattern, detail}, opts),
    do:
      generic_pattern_only_failure(
        :forced_pattern_not_in_pattern,
        detail,
        opts
      )

  def from_error({:named_implicit_not_in_pattern, detail}, opts),
    do:
      generic_pattern_only_failure(
        :named_implicit_not_in_pattern,
        detail,
        opts
      )

  def from_error(error, _opts),
    do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp pattern_only_syntax(kind, context, opts) do
    whole = Map.get(context, :span) || Keyword.get(opts, :span)
    opener = Map.get(context, :opener_span)
    name_span = Map.get(context, :name_span)
    body_span = Map.get(context, :body_span)

    {title, body, primary_span, primary_message, labels, hint} =
      case kind do
        :forced_pattern ->
          {
            "Forced value appears outside a pattern",
            "A leading dot marks a value that a constructor pattern must equal; it does not evaluate or access that value as an ordinary expression. This dot appears in expression position, where there is no surrounding pattern to force.",
            opener || whole,
            "this dot introduces pattern-only syntax",
            [
              {body_span, "this is the value the pattern would be forced to equal"}
            ],
            "Remove the leading dot to use an ordinary expression, or move the forced value into a constructor pattern"
          }

        :named_implicit_pattern ->
          {
            "Named implicit appears outside a pattern",
            "`{name = pattern}` selects an implicit constructor field while matching a value. It cannot stand alone as an expression because no constructor pattern owns this implicit field.",
            whole,
            "this named implicit has no surrounding constructor pattern",
            [
              {name_span, "this names the constructor's implicit field"},
              {body_span, "this pattern would constrain that field"}
            ],
            "Move this named implicit inside a constructor pattern, or replace it with an ordinary expression"
          }
      end

    secondary =
      labels
      |> Enum.map(fn {span, message} ->
        if span == primary_span, do: nil, else: label(span, :secondary, message)
      end)
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: label(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: kind,
        expression_category: Map.get(context, :expression_category),
        checking: Map.get(context, :checking)
      }
    )
  end

  defp generic_pattern_only_failure(kind, detail, opts) do
    {title, body, message} =
      case kind do
        :forced_pattern_not_in_pattern ->
          {"Forced pattern is unavailable", "This forced pattern refers to a name that is not bound by the pattern.",
           "bind the name in the pattern before forcing it"}

        :named_implicit_not_in_pattern ->
          {"Named implicit is unavailable", "This named implicit is not bound by the surrounding pattern.",
           "bind the implicit in the pattern or remove the reference"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: fallback_label(opts, message),
      payload: %{kind: kind, detail: detail}
    )
  end

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

  defp fallback_label(opts, message),
    do: label(Keyword.get(opts, :span), :primary, message)
end
