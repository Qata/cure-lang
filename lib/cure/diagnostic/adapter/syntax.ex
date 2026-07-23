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

  def from_error({kind, details}, opts)
      when kind in [
             :bad_result_type,
             :non_integer_index,
             :unsupported_index_literal,
             :unsupported_index_expr,
             :unsupported_index_operator,
             :sigma_projection_needs_ctx
           ] and is_map(details),
      do: index_lowering_failure(kind, details, opts)

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

  defp index_lowering_failure(kind, details, opts) do
    {title, body, message, hint} = index_lowering_content(kind, details)
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: label(span, :primary, message),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: kind,
        shape: Map.get(details, :shape),
        family: Map.get(details, :family),
        value: Map.get(details, :value),
        subtype: Map.get(details, :subtype),
        operator: Map.get(details, :operator),
        projection: Map.get(details, :projection)
      }
    )
  end

  defp index_lowering_content(:bad_result_type, details) do
    family = Map.get(details, :family)

    {
      "Constructor result does not name its indexed family",
      "An indexed constructor must return `#{name(family)}(...)`, but this result has a different type shape. The constructor's result is where its refined indices are declared.",
      "return the indexed family from this constructor",
      "Write this result as `#{name(family)}(...)` with one value for every declared index"
    }
  end

  defp index_lowering_content(:non_integer_index, details) do
    value = name(Map.get(details, :value))

    {
      "Dependent index must be a whole number",
      "`#{value}` is fractional, but a numeric dependent index denotes a natural number. Fractional values cannot identify a constructor position or bounded size.",
      "this index is not a whole number",
      "Use a non-negative integer index, or change the indexed family to carry a different numeric type"
    }
  end

  defp index_lowering_content(:unsupported_index_literal, details) do
    subtype = details |> Map.get(:subtype) |> name()

    {
      "Literal cannot be used as a dependent index",
      "A `#{subtype}` literal has no supported type-level representation in this index position. Index literals must have a representation the kernel can check and normalize.",
      "this literal is not supported in an index",
      "Use a constructor or supported numeric index, or bind this information in an ordinary runtime field"
    }
  end

  defp index_lowering_content(:unsupported_index_expr, _details) do
    {
      "Expression cannot be lowered as a dependent index",
      "This expression form has no syntax-directed type-level lowering. Dependent indices may use bound names, constructors, total function applications, supported propositions, and dependent type formers.",
      "this expression is not available at the type level",
      "Move the computation into a total named function, then call that function from the index"
    }
  end

  defp index_lowering_content(:unsupported_index_operator, details) do
    operator = details |> Map.get(:operator) |> name()

    {
      "`#{operator}` is not supported directly in an index",
      "The index lowerer recognizes comparisons and boolean connectives directly, but `#{operator}` has no unambiguous type-level builtin in this position.",
      "this operator has no direct index lowering",
      "Define the computation as a total function and call it from the index instead"
    }
  end

  defp index_lowering_content(:sigma_projection_needs_ctx, details) do
    projection = Map.get(details, :projection)

    {
      "Tuple projection lacks a checking context",
      "The `.#{projection}` projection needs the surrounding dependent checking context to infer its erased component types, but this index position does not provide one.",
      "this projection cannot infer its dependent components here",
      "Bind the projected component explicitly, or move the projection into a checked return-type index"
    }
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

  defp name(value) when is_atom(value), do: Atom.to_string(value)
  defp name(value) when is_binary(value), do: value
  defp name(value), do: inspect(value)
end
