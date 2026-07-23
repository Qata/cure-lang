defmodule Cure.Diagnostic.Adapter.Type do
  @moduledoc """
  Converts canonical contextual type failures into E093 diagnostics.

  This module owns the user-facing expected/found comparison. Core remains
  available only in an explicitly requested debug payload.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, ExpectationOrigin, Label, Span, Suggestion, TypeProblem}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error(%TypeProblem{} = problem, opts) do
    actual_surface = surface_type(problem.actual)
    expected_surface = surface_type(problem.expected)
    primary_span = problem.span || Keyword.get(opts, :span)

    primary =
      if primary_span do
        %Label{span: primary_span, style: :primary, message: label(problem.origin)}
      end

    payload =
      %{
        expected_surface: expected_surface,
        actual_surface: actual_surface,
        origin: Map.from_struct(problem.origin),
        expression_category: problem.expression
      }
      |> maybe_put_debug(problem.expected, problem.actual, problem.debug, opts)

    Diagnostic.new(
      code: "E093",
      key: problem.kind,
      severity: :error,
      title: title(problem.origin),
      body: Doc.stack([Doc.paragraph(context(problem.origin)), comparison_doc(problem.expected, problem.actual)]),
      primary: primary,
      secondary: expectation_labels(problem.origin, primary_span, problem.related),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: payload
    )
  end

  def from_error({:conversion_failure, actual, expected}, opts) do
    payload =
      %{
        expected_surface: surface_type(expected),
        actual_surface: surface_type(actual)
      }
      |> maybe_put_debug(expected, actual, %{}, opts)

    Diagnostic.new(
      code: "E093",
      key: :conversion_failure,
      severity: :error,
      title: "Type mismatch",
      body: comparison_doc(expected, actual),
      primary: primary(opts, "this expression has the wrong type"),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: payload
    )
  end

  def from_error(
        {:source_context, {:conversion_failure, actual, expected} = reason, context},
        opts
      )
      when is_map(context) do
    case Map.get(context, :expectation_origin) do
      nil ->
        raise Cure.Diagnostic.UnhandledError,
          error: {:source_context, reason, context}

      origin ->
        from_error(
          %TypeProblem{
            kind: :conversion_failure,
            actual: actual,
            expected: expected,
            origin: %ExpectationOrigin{
              kind: origin,
              span: Map.get(context, :expectation_span),
              owner: Map.get(context, :checking),
              index: Map.get(context, :argument_index)
            },
            expression: Map.get(context, :expression_category, :expression),
            span: Keyword.get(opts, :span, Map.get(context, :span)),
            debug: %{cause: reason, checking: Map.get(context, :checking)}
          },
          opts
        )
    end
  end

  def from_error({:lambda_expected_pi, %{expected: expected} = details}, opts) do
    expected_surface = surface_type(expected)
    parameter_index = Map.get(details, :parameter_index, 0)

    secondary =
      case Map.get(details, :parameter_span) do
        %Span{} = span ->
          [%Label{span: span, style: :secondary, message: "this parameter needs a function input type"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Lambda needs a function type",
      body:
        Doc.paragraph(
          "This lambda has parameter #{parameter_index + 1}, but its surrounding context expects `#{expected_surface}` at that point. An untyped lambda parameter can only be checked when the expected type provides a corresponding function input."
        ),
      primary: primary(opts, "this lambda is used where a non-function value is required"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Pass this lambda to a function-valued parameter, or replace it with a `#{expected_surface}` value",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :lambda_expected_pi,
        expected_surface: expected_surface,
        parameter_index: parameter_index
      }
    )
  end

  def from_error({:lambda_expected_pi, expected}, opts),
    do: from_error({:lambda_expected_pi, %{expected: expected, parameter_index: 0}}, opts)

  def from_error(:branch_type, opts), do: branch_failure(%{}, opts)

  def from_error({:source_context, :branch_type, context}, opts) when is_map(context),
    do: branch_failure(context, opts)

  def from_error({:source_context, {:branch_type, details}, context}, opts) when is_map(context),
    do: branch_failure(Map.put(context, :branch_details, details), opts)

  def from_error({kind, operator}, opts)
      when kind in [:unsupported_operand_type, :no_operator_meaning],
      do: operator_failure(kind, operator, %{}, opts)

  def from_error({:source_context, {kind, operator}, context}, opts)
      when kind in [:unsupported_operand_type, :no_operator_meaning] and is_map(context),
      do: operator_failure(kind, operator, context, opts)

  def from_error({:no_instance, interface, head}, opts),
    do: instance_failure(interface, head, %{}, opts)

  def from_error({:source_context, {:no_instance, interface, head}, context}, opts)
      when is_map(context),
      do: instance_failure(interface, head, context, Keyword.put_new(opts, :span, Map.get(context, :span)))

  def from_error({:no_matching_overload, name, arguments}, opts),
    do: overload_mismatch(%{name: name, arguments: arguments, candidates: []}, opts)

  def from_error({:no_matching_overload, %{name: _name} = details}, opts),
    do: overload_mismatch(details, opts)

  def from_error({:ambiguous_overload, name, owners}, opts),
    do: overload_ambiguity(name, owners, opts)

  def from_error({:applied_non_function, details}, opts) when is_map(details),
    do: non_callable(details, %{}, opts)

  def from_error({:source_context, {:applied_non_function, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: non_callable(details, context, opts)

  def from_error({:cannot_infer_match_type, %{reason: reason} = details}, opts)
      when reason in [:no_constructor_arm, :scrutinee_not_data],
      do: match_inference(reason, details, opts)

  def from_error({:cannot_infer_match_type, _legacy_expression}, opts),
    do: match_inference(:unknown, %{}, opts)

  def from_error({:source_context, :with_scrutinee_not_data, context}, opts)
      when is_map(context),
      do: non_data_with(context, opts)

  def from_error({:source_context, :match_scrutinee_not_data, context}, opts)
      when is_map(context),
      do: non_data_match(context, opts)

  def from_error({:source_context, :with_mixed_rematch_arms, context}, opts)
      when is_map(context),
      do: mixed_with_arms(context, opts)

  def from_error(
        {:source_context, {:with_indexed_scrutinee_unsupported, family}, context},
        opts
      )
      when is_map(context),
      do: indexed_with_proof(family, context, opts)

  def from_error(
        {:source_context, {:cannot_infer_dependent_match, _inferred_type}, context},
        opts
      )
      when is_map(context),
      do: dependent_match_inference(context, opts)

  def from_error({:source_context, {:record_update_base_mismatch, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: record_update_base(details, context, opts)

  def from_error({:source_context, {:projection_not_a_record, record}, context}, opts)
      when is_map(context),
      do: projection_receiver(record, context, opts)

  def from_error({:source_context, {:projection_non_record, field}, context}, opts)
      when is_map(context),
      do: projection_receiver(nil, Map.put_new(context, :field, field), opts)

  def from_error({:source_context, {:dependent_record_projection, record, field}, context}, opts)
      when is_map(context),
      do: dependent_projection(record, field, context, opts)

  def from_error({:typed_pattern_type_mismatch, type_ast}, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Pattern annotation does not match",
      body: Doc.paragraph("This pattern's annotation is incompatible with the value it matches."),
      primary: primary(opts, "change the pattern or its type annotation"),
      payload: %{kind: :typed_pattern, annotation: pattern_annotation(type_ast)}
    )
  end

  def from_error(
        {:source_context, {:typed_pattern_type_mismatch, _type_ast}, %{field_type: field_type} = context},
        opts
      )
      when not is_nil(field_type),
      do: typed_pattern_annotation(context, opts)

  def from_error(
        {:source_context, {:forced_pattern_not_in_pattern, _meta},
         %{forced_pattern_position: :positional_constructor_argument} = context},
        opts
      ),
      do: positional_forced_pattern(context, opts)

  def from_error(
        {:source_context, {:forced_pattern_mismatch, actual, expected}, %{forced_pattern_span: _} = context},
        opts
      ),
      do: forced_pattern_mismatch(actual, expected, context, opts)

  def from_error({:source_context, {:forced_pattern_mismatch, actual, expected}, context}, opts)
      when is_map(context) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Forced pattern does not match",
      body: Doc.paragraph("This forced pattern does not match the value's expected type."),
      primary:
        primary(Keyword.put_new(opts, :span, Map.get(context, :span)), "change the forced pattern or its expected type"),
      payload: %{kind: :forced_pattern_mismatch, actual: actual, expected: expected}
    )
  end

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp typed_pattern_annotation(context, opts) do
    constructor = short_name(Map.get(context, :constructor, :constructor))
    binder = name(Map.get(context, :binder, "field"))
    annotated = pattern_type(Map.get(context, :annotated_type))
    field_type = pattern_type(Map.get(context, :field_type))
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :annotation_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(context, :binder_span) || Map.get(context, :typed_pattern_span),
          primary_span,
          "`#{binder}` is the field being annotated"
        ),
        related_label(
          Map.get(context, :constructor_pattern_span) || Map.get(context, :constructor_name_span),
          primary_span,
          "`#{constructor}` provides this field as `#{field_type}`"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{binder}` is annotated as `#{annotated}`, but `#{constructor}` stores `#{field_type}`",
      body:
        Doc.paragraph(
          "Visible field #{argument_index + 1} of `#{constructor}` has type `#{field_type}`. This pattern annotates `#{binder}` as `#{annotated}`, so the annotation cannot describe the value selected by the constructor."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this says `#{annotated}`, but the constructor field is `#{field_type}`"
          }
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Change the annotation to `#{field_type}`, or remove it and let `#{constructor}` determine the field type",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :typed_pattern_type_mismatch,
        constructor: constructor,
        binder: binder,
        argument_index: argument_index,
        annotated: annotated,
        field_type: field_type,
        checking: Map.get(context, :checking, :pattern)
      }
    )
  end

  defp positional_forced_pattern(context, opts) do
    constructor = short_name(Map.get(context, :constructor, :constructor))
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :constructor_span) do
        %Span{} = span when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "this constructor pattern supplies positional fields"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Dot pattern must name an implicit field",
      body:
        Doc.paragraph(
          "Field #{argument_index + 1} of `#{constructor}` is positional. A dot pattern checks a value that constructor-index refinement already determined, so it must be written inside a named implicit pattern such as `{index = .value}`."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{span: primary_span, style: :primary, message: "this forced check is in a positional field"}
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Bind this positional field normally, or move the dot check to the constructor's corresponding named implicit field",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :positional_forced_pattern,
        constructor: constructor,
        argument_index: argument_index,
        expectation_origin: :pattern
      }
    )
  end

  defp forced_pattern_mismatch(actual, expected, context, opts) do
    constructor = short_name(Map.get(context, :constructor, :constructor))
    implicit_name = name(Map.get(context, :implicit_name, "index"))
    actual_surface = Map.get(context, :written_surface) || pattern_type(actual)
    expected_surface = Map.get(context, :expected_surface) || pattern_type(expected)
    primary_span = Map.get(context, :forced_pattern_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        related_label(
          Map.get(context, :named_implicit_span),
          primary_span,
          "this check targets the hidden `#{implicit_name}` field"
        ),
        related_label(
          Map.get(context, :constructor_name_span),
          primary_span,
          "`#{constructor}` fixes the value of `#{implicit_name}` from the matched index"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Forced `#{implicit_name}` does not match `#{constructor}`",
      body:
        Doc.paragraph(
          "The dot expression denotes `#{actual_surface}`, but matching `#{constructor}` fixes `#{implicit_name}` as `#{expected_surface}`. A forced pattern checks an index already determined by the scrutinee; it cannot choose a different value."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this forced value disagrees with the index fixed here"
          }
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Change the dot expression to the value fixed by `#{constructor}`, or bind `#{implicit_name}` without a dot when it is not forced",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :forced_pattern_mismatch,
        constructor: constructor,
        implicit_name: implicit_name,
        actual: actual_surface,
        expected: expected_surface,
        expectation_origin: :pattern
      }
    )
  end

  defp pattern_type({:data, family, parameters, indices}) do
    arguments = Enum.map(parameters ++ indices, &pattern_type/1)
    application(short_name(family), arguments)
  end

  defp pattern_type({:ctor, constructor, arguments}),
    do: application(short_name(constructor), Enum.map(arguments, &pattern_type/1))

  defp pattern_type({:global, global}), do: short_name(global)
  defp pattern_type({:meta, _id}), do: "?"
  defp pattern_type(other), do: surface_type(other)

  defp application(head, []), do: head
  defp application(head, arguments), do: "#{head}(#{Enum.join(arguments, ", ")})"

  defp pattern_annotation({:variable, _meta, variable}), do: name(variable)
  defp pattern_annotation(type), do: surface_type(type)

  defp record_update_base(details, context, opts) do
    record = Map.fetch!(details, :record)
    actual = Map.fetch!(details, :actual)
    record_surface = short_name(record)
    actual_surface = if is_atom(actual), do: short_name(actual), else: surface_type(actual)
    base_span = Map.get(context, :base_span) || Map.get(context, :span)
    record_span = Map.get(context, :record_name_span)

    secondary =
      case record_span do
        %Span{} = span when span != base_span ->
          [%Label{span: span, style: :secondary, message: "this update constructs `#{record_surface}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{record_surface}` update needs a `#{record_surface}` value",
      body:
        Doc.paragraph(
          "The value before `|` has type `#{actual_surface}`, but a `#{record_surface}` update must start from another `#{record_surface}` value."
        ),
      primary:
        if(match?(%Span{}, base_span),
          do: %Label{span: base_span, style: :primary, message: "this value has type `#{actual_surface}`"},
          else: primary(opts, "use a `#{record_surface}` value here")
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: "Use a `#{record_surface}` value before `|`", applicability: :manual}],
      payload: %{
        kind: :record_update_base_mismatch,
        record: record,
        record_surface: record_surface,
        actual: actual,
        actual_surface: actual_surface,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp projection_receiver(record, context, opts) do
    field = context |> Map.get(:field) |> name()
    receiver_span = Map.get(context, :receiver_span) || Map.get(context, :span)
    field_span = Map.get(context, :field_span)
    actual_type = if record, do: short_name(record)

    {title, body, receiver_message} =
      if actual_type do
        {
          "Cannot project `#{field}` from `#{actual_type}`",
          "This value has type `#{actual_type}`, which is not a record and therefore has no field named `#{field}`.",
          "this value has type `#{actual_type}`, not a record"
        }
      else
        {
          "Record projection requires a record",
          "This value is not a record, so it has no field named `#{field}`.",
          "this value is not a record"
        }
      end

    secondary =
      case field_span do
        %Span{} = span when span != receiver_span ->
          [%Label{span: span, style: :secondary, message: "this projection asks for field `#{field}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        if(match?(%Span{}, receiver_span),
          do: %Label{span: receiver_span, style: :primary, message: receiver_message},
          else: primary(opts, receiver_message)
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: "Use a record value before `.#{field}`, or remove the projection", applicability: :manual}
      ],
      payload: %{
        kind: if(record, do: :projection_not_a_record, else: :projection_non_record),
        actual_type: actual_type,
        actual_type_id: record,
        field: field,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp dependent_projection(record, field, context, opts) do
    record_name = short_name(record)
    field = name(field)
    dependencies = Map.get(context, :dependent_fields, [])
    dependency_list = Enum.map_join(dependencies, ", ", &"`#{&1}`")
    primary_span = Map.get(context, :field_span) || Map.get(context, :span) || Keyword.get(opts, :span)
    projected_site = Map.get(context, :projected_field_declaration, %{})
    dependent_sites = Map.get(context, :dependent_field_declarations, %{})

    dependency_phrase =
      case dependencies do
        [dependency] -> "the earlier field `#{dependency}`"
        [] -> "an earlier field"
        _ -> "the earlier fields #{dependency_list}"
      end

    secondary =
      [
        related_label(
          Map.get(context, :receiver_span),
          primary_span,
          "this value has dependent record type `#{record_name}`"
        ),
        related_label(
          site_span(projected_site),
          primary_span,
          "`#{field}` is declared with a type that depends on #{dependency_phrase}"
        )
      ] ++
        Enum.map(dependencies, fn dependency ->
          related_label(
            dependent_sites |> Map.get(dependency) |> site_span(),
            primary_span,
            "`#{dependency}` supplies part of `#{field}`'s type"
          )
        end)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{field}` cannot be projected without its dependency",
      body:
        Doc.paragraph(
          "The type of `#{record_name}.#{field}` depends on #{dependency_phrase}. Projecting only `#{field}` would discard the value needed to state its result type. Destructure the record so the dependent fields remain in scope together."
        ),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this projection separates `#{field}` from #{dependency_phrase}"
          }
        ),
      secondary: Enum.reject(secondary, &is_nil/1),
      suggestions: [
        %Suggestion{
          message: "Pattern-match `#{record_name}` and bind #{Enum.join(dependencies ++ [field], ", ")} together",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :dependent_record_projection,
        record: record_name,
        field: field,
        dependencies: dependencies,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp related_label(%Span{} = span, primary_span, message) when span != primary_span,
    do: %Label{span: span, style: :secondary, message: message}

  defp related_label(_span, _primary_span, _message), do: nil

  defp site_span(%{type_span: %Span{} = span}), do: span
  defp site_span(%{span: %Span{} = span}), do: span
  defp site_span(_site), do: nil

  defp short_name(value), do: value |> name() |> String.split("#") |> List.last()

  defp dependent_match_inference(context, opts) do
    branch = Enum.find(Map.get(context, :branch_patterns, []), &match?(%{span: %Span{}}, &1))
    match_span = Map.get(context, :opener_span) || Map.get(context, :span) || Keyword.get(opts, :span)
    branch_name = branch && Map.get(branch, :name)

    branch_message =
      if branch_name do
        "the `#{branch_name}` branch returns a type tied to values introduced by its pattern"
      else
        "this branch returns a type tied to values introduced by its pattern"
      end

    {primary, secondary} =
      case branch do
        %{span: %Span{} = branch_span} ->
          related =
            if match?(%Span{}, match_span) and match_span != branch_span do
              [%Label{span: match_span, style: :secondary, message: "this match has no expected result type"}]
            else
              []
            end

          {%Label{span: branch_span, style: :primary, message: branch_message}, related}

        _ ->
          {primary(Keyword.put(opts, :span, match_span), "this match needs an expected result type"), []}
      end

    checking = Map.get(context, :checking)
    owner = if checking, do: " `#{name(checking)}`", else: ""

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Dependent match result needs an annotation",
      body:
        Doc.paragraph(
          "Cure inferred a branch result whose type depends on values introduced by that branch's constructor pattern. Those values do not exist outside the branch, so Cure cannot choose one result type for#{owner} without an annotation."
        ),
      primary: primary,
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Add a result annotation to `#{name(checking || :the_enclosing_declaration)}` that states the indexed result shared by every branch",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :cannot_infer_dependent_match,
        checking: checking,
        expression_category: Map.get(context, :expression_category, :pattern_match),
        branch: branch_name
      }
    )
  end

  defp indexed_with_proof(family, context, opts) do
    family = family |> name() |> String.split("#") |> List.last()
    proof_name = Map.get(context, :proof_name)
    proof_span = Map.get(context, :proof_span) || Map.get(context, :span)
    scrutinee_span = Map.get(context, :scrutinee_span)

    proof_binding =
      if proof_name,
        do: "The `proof #{proof_name}` clause asks Cure to bind a value equation in every branch.",
        else: "This `with` asks Cure to transport a value equation into every branch."

    branch_labels =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.flat_map(fn
        %{span: %Span{} = span} ->
          [%Label{span: span, style: :secondary, message: "this branch would need an indexed value equation"}]

        _ ->
          []
      end)

    scrutinee_label =
      case scrutinee_span do
        %Span{} = span ->
          [%Label{span: span, style: :secondary, message: "this value belongs to indexed family `#{family}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Indexed with cannot bind a value proof",
      body:
        Doc.stack([
          Doc.paragraph(proof_binding),
          Doc.paragraph(
            "`#{family}` is indexed, so its branch constructors can refine type indices. Cure cannot also synthesize the whole-value equation requested by this form."
          )
        ]),
      primary: %Label{
        span: proof_span || Keyword.get(opts, :span),
        style: :primary,
        message: "this proof binding is unsupported for an indexed `with`"
      },
      secondary: scrutinee_label ++ branch_labels,
      suggestions: [
        %Suggestion{
          message:
            "Remove `proof #{proof_name || "..."}` when the equation is unused, or rewrite every branch in the indexed LHS-rematch form",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :with_indexed_scrutinee_unsupported,
        checking: Map.get(context, :checking),
        family: family,
        proof_name: proof_name,
        branch_count: length(branch_labels)
      }
    )
  end

  defp mixed_with_arms(context, opts) do
    arms =
      context
      |> Map.get(:with_arms, [])
      |> Enum.filter(&match?(%{style: style, span: %Span{}} when style in [:ordinary, :rematch], &1))

    frequencies = Enum.frequencies_by(arms, & &1.style)

    outlier_index =
      Enum.find_index(arms, fn arm ->
        Map.get(frequencies, arm.style) == 1 and
          Enum.any?(frequencies, fn {style, count} -> style != arm.style and count > 1 end)
      end)

    labels =
      arms
      |> Enum.with_index()
      |> Enum.map(fn {arm, index} ->
        %{span: arm.span, message: with_arm_label(arm.style, index == outlier_index), index: index}
      end)

    {primary, secondary} =
      case labels do
        [] ->
          {primary(Keyword.put_new(opts, :span, Map.get(context, :span)), "use one branch form throughout"), []}

        available ->
          chosen_index = outlier_index || 0
          chosen = Enum.at(available, chosen_index)

          secondary =
            available
            |> Enum.reject(&(&1.index == chosen_index))
            |> Enum.map(&%Label{span: &1.span, style: :secondary, message: &1.message})

          {%Label{span: chosen.span, style: :primary, message: chosen.message}, secondary}
      end

    body =
      if outlier_index do
        style = arms |> Enum.at(outlier_index) |> Map.fetch!(:style)

        Doc.stack([
          Doc.paragraph(
            "Possible outlier: only one branch uses the #{with_arm_style(style)} form; the other branches use the other form."
          ),
          Doc.paragraph(
            "A `with` block must use one shape throughout: either `Pattern -> body` in every branch, or `ParentPattern | WithPattern -> body` in every branch."
          )
        ])
      else
        Doc.stack([
          Doc.paragraph("These branches mix the two forms accepted by a `with` block."),
          Doc.paragraph(
            "Use either `Pattern -> body` in every branch, or `ParentPattern | WithPattern -> body` in every branch."
          )
        ])
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With branches use incompatible forms",
      body: body,
      primary: primary,
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Make every branch use the same `with` form; changing forms may change which values are refined",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :with_mixed_rematch_arms,
        checking: Map.get(context, :checking),
        branch_forms: Enum.map(arms, & &1.style),
        outlier_branch: outlier_index
      }
    )
  end

  defp with_arm_label(style, true),
    do: "possible outlier: this is the only #{with_arm_style(style)} branch"

  defp with_arm_label(:ordinary, false), do: "ordinary branch: `Pattern -> body`"
  defp with_arm_label(:rematch, false), do: "rematch branch: `ParentPattern | WithPattern -> body`"

  defp with_arm_style(:ordinary), do: "ordinary `Pattern -> body`"
  defp with_arm_style(:rematch), do: "rematch `ParentPattern | WithPattern -> body`"

  defp non_data_with(context, opts) do
    actual_type = context |> Map.get(:actual_type) |> surface_type()
    scrutinee_span = Map.get(context, :scrutinee_span) || Map.get(context, :span)
    form = Map.get(context, :with_form, :ordinary)

    branch_labels =
      context
      |> Map.get(:with_arms, [])
      |> Enum.flat_map(fn
        %{span: %Span{} = span} ->
          [%Label{span: span, style: :secondary, message: non_data_with_branch_label(form)}]

        _ ->
          []
      end)

    opener_label =
      case Map.get(context, :opener_span) do
        %Span{} = span when span != scrutinee_span ->
          [%Label{span: span, style: :secondary, message: "this `with` tries to refine the value by constructors"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With requires a data value",
      body:
        Doc.stack([
          Doc.paragraph(
            "This `with` scrutinee has type `#{actual_type}`, which does not provide data constructors to refine."
          ),
          Doc.paragraph(non_data_with_explanation(form))
        ]),
      primary: %Label{
        span: scrutinee_span || Keyword.get(opts, :span),
        style: :primary,
        message: "`#{actual_type}` cannot be split into constructor branches"
      },
      secondary: opener_label ++ branch_labels,
      suggestions: [
        %Suggestion{
          message:
            "Use `pickup` for conditions on primitive values, or remove `with` when no constructor refinement is needed",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :with_scrutinee_not_data,
        checking: Map.get(context, :checking),
        actual_type: actual_type,
        with_form: form,
        branch_count: length(branch_labels)
      }
    )
  end

  defp non_data_match(context, opts) do
    actual_type = context |> Map.get(:actual_type) |> surface_type()
    scrutinee_span = Map.get(context, :scrutinee_span) || Map.get(context, :span)

    constructor_patterns =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.filter(&(Map.get(&1, :kind) == :constructor and match?(%Span{}, Map.get(&1, :pattern_span))))

    pattern_labels =
      Enum.map(constructor_patterns, fn pattern ->
        %Label{
          span: pattern.pattern_span,
          style: :secondary,
          message: "`#{Map.get(pattern, :name, "this pattern")}` expects a data constructor"
        }
      end)

    {primary, remaining_patterns} =
      case pattern_labels do
        [%Label{} = first | rest] ->
          {%Label{first | style: :primary, message: "this constructor pattern cannot match `#{actual_type}`"}, rest}

        [] ->
          {%Label{
             span: scrutinee_span || Keyword.get(opts, :span),
             style: :primary,
             message: "`#{actual_type}` does not provide data constructors"
           }, []}
      end

    scrutinee_label =
      if match?(%Span{}, scrutinee_span) and scrutinee_span != primary.span do
        [%Label{span: scrutinee_span, style: :secondary, message: "this expression has type `#{actual_type}`"}]
      else
        []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Constructor patterns cannot match #{actual_type}",
      body:
        Doc.stack([
          Doc.paragraph(
            "The value being matched has type `#{actual_type}`, but these branches try to deconstruct it with data constructors."
          ),
          Doc.paragraph(
            "Constructor patterns work only when the scrutinee belongs to the same constructor-defined data type."
          )
        ]),
      primary: primary,
      secondary: scrutinee_label ++ remaining_patterns,
      suggestions: [
        %Suggestion{
          message:
            "Use a variable or wildcard for the whole `#{actual_type}` value, a supported literal pattern for a primitive, or match constructor-defined data",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :match_scrutinee_not_data,
        checking: Map.get(context, :checking),
        actual_type: actual_type,
        constructor_patterns: Enum.map(constructor_patterns, &Map.get(&1, :name))
      }
    )
  end

  defp non_data_with_explanation(:rematch),
    do:
      "A rematch branch can restate the parent patterns only when the value after `with` belongs to a constructor-defined data type."

  defp non_data_with_explanation(_ordinary),
    do:
      "A `with` block refines its surrounding goal through the constructors of the value after `with`; it is not a general conditional."

  defp non_data_with_branch_label(:rematch),
    do: "this rematch branch needs a constructor-defined `with` value"

  defp non_data_with_branch_label(_ordinary),
    do: "this branch cannot refine a value without constructors"

  defp match_inference(reason, details, opts) do
    {title, body, primary_message, hint} =
      case reason do
        :no_constructor_arm ->
          {
            "Match result needs an annotation",
            "Cure is inferring the result type of this match, but none of its patterns names a constructor. A wildcard or variable arm can handle values of many data types, so it does not reveal the family or dependent result that the branches must share.",
            "this match has no constructor arm to guide inference",
            "Add a result annotation to the enclosing declaration, or include a constructor pattern that identifies the matched data family"
          }

        :scrutinee_not_data ->
          {
            "Match target does not have a data type",
            "Cure can only infer an unannotated match from a scrutinee whose type has constructors. This value does not infer as a data family, so its patterns cannot determine a shared result type.",
            "this match cannot infer a result from its target",
            "Match a value of a declared data type, or add a result annotation that gives this match an expected type"
          }

        :unknown ->
          {
            "Cannot infer match type",
            "Cure cannot determine one result type shared by every branch of this match.",
            "add an annotation or make the branches agree",
            "Add a result annotation to the enclosing declaration"
          }
      end

    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: if(match?(%Span{}, span), do: %Label{span: span, style: :primary, message: primary_message}),
      secondary: match_inference_labels(reason, details, span),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :cannot_infer_match_type,
        reason: reason,
        expression_category: Map.get(details, :expression_category, :pattern_match)
      }
    )
  end

  defp match_inference_labels(:no_constructor_arm, details, primary_span) do
    details
    |> Map.get(:branch_spans, [])
    |> Enum.filter(&(match?(%Span{}, &1) and &1 != primary_span))
    |> Enum.map(&%Label{span: &1, style: :secondary, message: "this pattern does not identify a constructor"})
  end

  defp match_inference_labels(:scrutinee_not_data, details, primary_span) do
    case Map.get(details, :scrutinee_span) do
      %Span{} = span when span != primary_span ->
        [%Label{span: span, style: :secondary, message: "this value does not infer as a data family"}]

      _ ->
        []
    end
  end

  defp match_inference_labels(_reason, _details, _primary_span), do: []

  defp non_callable(details, context, opts) do
    index = Map.get(details, :argument_index, 0)
    actual = surface_type(Map.get(details, :actual))
    callee = Map.get(context, :callee_name)
    callee_span = Map.get(context, :callee_span)
    argument_span = Map.get(context, :argument_span)
    fallback_span = Map.get(context, :span) || Keyword.get(opts, :span)

    {title, body, primary_span, primary_message, related, hint} =
      if index == 0 do
        {
          "`#{actual}` value is not callable",
          "Parentheses apply a function or constructor, but this expression has type `#{actual}`. It cannot accept the argument written after it.",
          callee_span || fallback_span,
          "this expression has type `#{actual}`, not a function type",
          [{argument_span, "this argument has nowhere to go"}],
          "Remove the parentheses, or replace this expression with a function or constructor"
        }
      else
        callee_name = if callee, do: "`#{callee}`", else: "This call"

        {
          "#{callee_name} is given too many arguments",
          "After accepting #{index} #{if(index == 1, do: "argument", else: "arguments")}, #{callee_name} produces `#{actual}`. That result is not a function, so it cannot accept argument #{index + 1}.",
          argument_span || fallback_span,
          "this extra argument is applied to a `#{actual}` result",
          [{callee_span, "#{callee_name} has already produced its result before this argument"}],
          "Remove argument #{index + 1}, or call a function whose result accepts another argument"
        }
      end

    secondary =
      related
      |> Enum.filter(fn {span, _message} -> match?(%Span{}, span) and span != primary_span end)
      |> Enum.map(fn {span, message} -> %Label{span: span, style: :secondary, message: message} end)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        if(match?(%Span{}, primary_span),
          do: %Label{span: primary_span, style: :primary, message: primary_message}
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :applied_non_function,
        actual_type: actual,
        argument_index: index,
        callee: callee,
        expression_category: Map.get(context, :expression_category, :function_call)
      }
    )
  end

  defp instance_failure(interface, head, context, opts) do
    interface = name(interface)
    head = instance_head(head)

    {body, label, hint} =
      case head.kind do
        :type_variable ->
          {
            "This expression uses `#{interface}` operations on a type variable, but the surrounding function does not require `#{interface}` for that type.",
            "this operation requires `#{interface}` for its type variable",
            "Add a `where #{interface}(...)` constraint using this parameter's type variable"
          }

        :concrete ->
          {
            "No implementation of `#{interface}` is available for `#{head.surface}`. Cure needs one here to choose the behavior of this operation.",
            "this operation requires `#{interface}` for `#{head.surface}`",
            "Add or import `implementation #{interface} for #{head.surface}`"
          }
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "No `#{interface}` implementation found",
      body: Doc.paragraph(body),
      primary: primary(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :no_instance,
        interface: interface,
        head_kind: head.kind,
        head_surface: head.surface,
        head_id: head.id,
        expectation_origin: Map.get(context, :expectation_origin, :implicit),
        checking: Map.get(context, :checking)
      }
    )
  end

  defp instance_head({:rigid, index}) when is_integer(index),
    do: %{kind: :type_variable, surface: "a type variable", id: "rigid:#{index}"}

  defp instance_head(head) when is_atom(head) or is_binary(head) do
    canonical = name(head)
    surface = Cure.Elab.Name.base(head) || canonical
    %{kind: :concrete, surface: name(surface), id: canonical}
  end

  defp instance_head(head) do
    surface = surface_type(head)
    %{kind: :concrete, surface: surface, id: surface}
  end

  defp overload_mismatch(details, opts) do
    overload_name = name(details.name)

    arguments =
      details
      |> Map.get(:arguments, [])
      |> Enum.map(fn
        nil -> "unknown"
        type -> overload_type(type)
      end)

    candidates =
      details
      |> Map.get(:candidates, [])
      |> Enum.map(fn candidate ->
        owner = Map.get(candidate, :owner)
        prefix = if owner, do: "#{name(owner)}.", else: ""
        parameters = Enum.map_join(Map.get(candidate, :parameters, []), ", ", &overload_type/1)

        %{
          id: name(Map.get(candidate, :id, overload_name)),
          owner: if(owner, do: name(owner)),
          signature: "#{prefix}#{overload_name}(#{parameters})"
        }
      end)
      |> Enum.sort_by(& &1.signature)

    argument_text = if arguments == [], do: "unknown argument types", else: Enum.join(arguments, ", ")

    candidates_doc =
      case candidates do
        [] ->
          Doc.paragraph("No declared overload accepts these argument types.")

        available ->
          Doc.stack([
            Doc.paragraph("These overloads are available:"),
            Doc.bullet_list(Enum.map(available, &"`#{&1.signature}`"))
          ])
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "No overload of `#{overload_name}` matches",
      body:
        Doc.stack([
          Doc.paragraph("This call supplies argument types `#{argument_text}`."),
          candidates_doc
        ]),
      primary: primary(opts, "these arguments do not match any `#{overload_name}` overload"),
      suggestions: [
        %Suggestion{
          message: "Change the arguments to match one of the listed signatures",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :no_matching_overload,
        name: overload_name,
        arguments: arguments,
        candidates: candidates
      }
    )
  end

  defp overload_ambiguity(overload_name, owners, opts) do
    overload_name = name(overload_name)
    owners = owners |> List.wrap() |> Enum.map(&name/1) |> Enum.uniq() |> Enum.sort()
    candidates = Enum.map(owners, &qualified_candidate(&1, overload_name))

    {candidate_text, verb} =
      case candidates do
        [one] -> {"`#{one}`", "accepts"}
        [one, two] -> {"Both `#{one}` and `#{two}`", "accept"}
        many -> {"All of " <> Enum.map_join(many, ", ", &"`#{&1}`"), "accept"}
      end

    hint =
      case candidates do
        [one] -> "Qualify the call as `#{one}(...)`"
        [one, two] -> "Choose `#{one}(...)` or `#{two}(...)`"
        many -> "Qualify the call with one of: " <> Enum.map_join(many, ", ", &"`#{&1}(...)`")
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Call to `#{overload_name}` is ambiguous",
      body:
        Doc.paragraph(
          "#{candidate_text} #{verb} the arguments at this call site. Cure cannot choose one without changing the program's meaning."
        ),
      primary: primary(opts, "qualify this call with the module you intend"),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :ambiguous_overload,
        name: overload_name,
        owners: owners,
        qualified_candidates: candidates
      }
    )
  end

  defp overload_type(type) when is_atom(type) or is_binary(type),
    do: name(Cure.Elab.Name.base(type) || type)

  defp overload_type(type), do: surface_type(type)

  defp qualified_candidate(owner, overload_name) do
    if String.contains?(owner, ".#{overload_name}"), do: owner, else: "#{owner}.#{overload_name}"
  end

  defp operator_failure(kind, operator, context, opts) do
    spelling = name(operator)
    types = context |> Map.get(:operand_types, []) |> Enum.map(&surface_type/1)
    operator_span = Map.get(context, :operator_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    {title, body, primary_message, hint} = operator_copy(kind, spelling, types)

    secondary =
      context
      |> Map.get(:operand_spans, [])
      |> Enum.with_index()
      |> Enum.map(fn {span, index} ->
        side = if index == 0, do: "left", else: "right"

        message =
          case Enum.at(types, index) do
            nil -> "the #{side} operand is here"
            type -> "the #{side} operand has type `#{type}`"
          end

        if match?(%Span{}, span), do: %Label{span: span, style: :secondary, message: message}
      end)
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: if(kind == :unsupported_operand_type, do: :operator_type_mismatch, else: :operator_resolution),
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary:
        if(match?(%Span{}, operator_span),
          do: %Label{span: operator_span, style: :primary, message: primary_message}
        ),
      secondary: if(kind == :unsupported_operand_type, do: secondary, else: []),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind, operator: operator, operand_types: types}
    )
  end

  defp operator_copy(:unsupported_operand_type, spelling, types) do
    description =
      case types do
        [left, right] -> "`#{left}` on the left and `#{right}` on the right"
        _ -> "the operand types used here"
      end

    {
      "`#{spelling}` does not support these operands",
      "The `#{spelling}` operator does not accept #{description}.",
      "this operator is not defined for these operand types",
      "Change the operand types, or use an operator or interface implementation defined for them"
    }
  end

  defp operator_copy(:no_operator_meaning, spelling, _types) do
    {
      "`#{spelling}` has no definition",
      "A fixity declaration tells Cure how to parse `#{spelling}`, but no function, constructor, or interface method with that name is available here.",
      "this operator has precedence, but no callable definition",
      "Define `#{spelling}` with two parameters, import its definition, or use an operator that is in scope"
    }
  end

  defp branch_failure(context, opts) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))
    branches = Keyword.get(opts, :branch_patterns, Map.get(context, :branch_patterns, []))
    branch_names = Enum.map(branches, &branch_name/1)
    checking = Map.get(context, :checking)
    subject = if checking, do: " in `#{checking}`", else: ""
    details = Map.get(context, :branch_details, %{})
    branch_details = Map.get(details, :branches, [])

    selected =
      case Enum.find(branch_details, &match?({:error, _}, Map.get(&1, :status))) do
        nil -> List.first(branch_details, details)
        detail -> detail
      end

    singleton_branches = singleton_type_branches(branch_details)

    failing =
      Map.get(selected, :constructor) ||
        case singleton_branches do
          [{constructor, _type}] -> constructor
          _ -> nil
        end

    actual = Map.get(selected, :actual)
    expected = Map.get(selected, :expected)

    detail =
      branch_detail(singleton_branches, failing, actual, expected, branch_names)

    labels =
      branches
      |> Enum.map(fn branch ->
        branch_name = branch_name(branch)

        message =
          if same_branch?(branch_name, failing),
            do: "possible outlier: this branch has the incompatible type",
            else: "compare this branch with the declared result"

        %{span: branch_span(branch), name: branch_name, message: message}
      end)
      |> Enum.reject(&is_nil(&1.span))
      |> Enum.sort_by(fn item -> if String.starts_with?(item.message, "possible outlier"), do: 0, else: 1 end)

    {primary, secondary} = branch_labels(labels, failing, opts)
    dependent? = Map.get(context, :expectation_origin) == :dependent_branch

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title:
        if(dependent?,
          do: "Dependent branch has the wrong result#{subject}",
          else: "Pattern branches disagree#{subject}"
        ),
      body:
        Doc.stack([
          Doc.paragraph(detail),
          Doc.paragraph(
            if dependent?,
              do:
                "This constructor refines indices in the branch context. Check the authored branch against the resulting specialized proposition.",
              else: "Check each branch expression against the result type written after the function name."
          )
        ]),
      primary: primary,
      secondary: secondary,
      payload: %{
        kind: :branch_type,
        branches: branch_names,
        failing_branch: failing,
        actual_surface: if(actual, do: surface_type(actual)),
        expected_surface: if(expected, do: surface_type(expected)),
        branch_types: branch_type_payload(branch_details),
        checking: checking,
        expression_category: Map.get(context, :expression_category),
        expectation_origin: Map.get(context, :expectation_origin)
      }
    )
  end

  defp branch_detail([{constructor, type}], _failing, _actual, _expected, _names),
    do:
      "Possible outlier: only the `#{name(constructor)}` branch has type `#{type}`; check it against the other branches and the declared result."

  defp branch_detail(_singletons, constructor, actual, expected, _names)
       when not is_nil(constructor) and not is_nil(actual) and not is_nil(expected),
       do:
         "Possible outlier: the `#{name(constructor)}` branch has type `#{surface_type(actual)}`, but the declared result requires `#{surface_type(expected)}`."

  defp branch_detail(_singletons, _failing, _actual, _expected, [first, second | rest]) do
    names = Enum.map_join([first, second | rest], ", ", &"`#{&1}`")

    "The branches #{names} of this match are checked against the declared result, but at least one branch does not produce that result."
  end

  defp branch_detail(_singletons, _failing, _actual, _expected, _names),
    do: "Every branch of this match is checked against the declared result type."

  defp branch_labels([], _failing, opts),
    do: {primary(opts, "make these branches return the same type"), []}

  defp branch_labels(labels, failing, _opts) do
    {outliers, comparisons} = Enum.split_with(labels, &same_branch?(&1.name, failing))
    [chosen | rest] = if outliers == [], do: labels, else: outliers ++ comparisons

    primary = %Label{span: chosen.span, style: :primary, message: chosen.message}

    secondary =
      Enum.map(rest, &%Label{span: &1.span, style: :secondary, message: &1.message})

    {primary, secondary}
  end

  defp singleton_type_branches(details) do
    groups =
      details
      |> Enum.filter(&(not is_nil(Map.get(&1, :actual))))
      |> Enum.group_by(&surface_type(&1.actual))

    if map_size(groups) > 1 and Enum.any?(groups, fn {_type, entries} -> length(entries) > 1 end) do
      for {type, [entry]} <- groups, do: {entry.constructor, type}
    else
      []
    end
  end

  defp branch_type_payload(details) do
    Enum.map(details, fn detail ->
      %{
        branch: detail.constructor,
        status: detail.status,
        actual: if(detail.actual, do: surface_type(detail.actual)),
        expected: if(detail.expected, do: surface_type(detail.expected))
      }
    end)
  end

  defp branch_name(%{name: name}), do: to_string(name)
  defp branch_name(name), do: to_string(name)

  defp same_branch?(_name, nil), do: false

  defp same_branch?(branch, failing) do
    branch = to_string(branch)
    failing = to_string(failing)
    failing == branch or String.ends_with?(failing, "#" <> branch) or String.ends_with?(failing, "." <> branch)
  end

  defp branch_span(%{span: %Span{} = span}), do: span
  defp branch_span(_branch), do: nil

  @doc false
  @spec contextual_failure(atom(), map(), keyword(), {String.t(), String.t(), String.t()}) :: Diagnostic.t()
  def contextual_failure(kind, details, opts, {title, message, label}) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary(opts, label),
      suggestions: [
        %Suggestion{
          message: sentence_case(label),
          applicability: :manual
        }
      ],
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  @spec comparison_doc(term(), term()) :: Doc.t()
  def comparison_doc(expected, actual) do
    {expected_doc, actual_doc} = difference_docs(printable_core(expected), printable_core(actual), false)

    Doc.concat([
      Doc.concat(["Expected: ", expected_doc]),
      Doc.text("\n"),
      Doc.concat(["Found:    ", actual_doc])
    ])
  end

  defp difference_docs(expected, actual, _within_common?) when expected == actual do
    {plain_type_doc(expected), plain_type_doc(actual)}
  end

  defp difference_docs(
         {:data, name, expected_params, expected_indices},
         {:data, name, actual_params, actual_indices},
         _within_common?
       )
       when length(expected_params) == length(actual_params) and length(expected_indices) == length(actual_indices) do
    application_docs(Cure.Elab.Name.base(name), expected_params ++ expected_indices, actual_params ++ actual_indices)
  end

  defp difference_docs({:ctor, name, expected_args}, {:ctor, name, actual_args}, _within_common?)
       when length(expected_args) == length(actual_args) do
    application_docs(Cure.Elab.Name.base(name), expected_args, actual_args)
  end

  defp difference_docs({:app, expected_fun, expected_arg}, {:app, actual_fun, actual_arg}, _within_common?) do
    {expected_fun_doc, actual_fun_doc} = difference_docs(expected_fun, actual_fun, true)
    {expected_arg_doc, actual_arg_doc} = difference_docs(expected_arg, actual_arg, true)

    {
      Doc.concat([expected_fun_doc, Doc.text(" "), expected_arg_doc]),
      Doc.concat([actual_fun_doc, Doc.text(" "), actual_arg_doc])
    }
  end

  defp difference_docs(expected, actual, true) do
    {
      Doc.emphasis(:expected, plain_type_doc(expected)),
      Doc.emphasis(:observed, plain_type_doc(actual))
    }
  end

  defp difference_docs(expected, actual, false),
    do: {plain_type_doc(expected), plain_type_doc(actual)}

  defp application_docs(head, expected_args, actual_args) do
    {expected_args, actual_args} =
      expected_args
      |> Enum.zip(actual_args)
      |> Enum.map(&difference_docs(elem(&1, 0), elem(&1, 1), true))
      |> Enum.unzip()

    {application_doc(head, expected_args), application_doc(head, actual_args)}
  end

  defp application_doc(head, []), do: Doc.text(head)

  defp application_doc(head, args) do
    args_doc = args |> Enum.intersperse(Doc.text(", ")) |> Doc.concat()
    Doc.concat([Doc.text(head), Doc.text("("), args_doc, Doc.text(")")])
  end

  defp plain_type_doc(type) when is_binary(type), do: Doc.text(type)
  defp plain_type_doc(type), do: Doc.text(print_core(type))

  defp surface_type(type) when is_binary(type), do: type
  defp surface_type(type), do: print_core(type)

  defp print_core(term) do
    term
    |> printable_core()
    |> Cure.Core.Printer.print()
  rescue
    ArgumentError -> inspect(term)
  end

  defp printable_core(term) when is_tuple(term) do
    case elem(term, 0) do
      :var ->
        term

      tag ->
        case Atom.to_string(tag) do
          "v" <> _ -> Cure.Core.Quote.reify(term, 0)
          _ -> term
        end
    end
  end

  defp printable_core(term), do: term

  defp maybe_put_debug(payload, expected, actual, details, opts) do
    if Keyword.get(opts, :debug, false) do
      Map.put(payload, :debug, %{
        expected_core: inspect(expected),
        actual_core: inspect(actual),
        details: details
      })
    else
      payload
    end
  end

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span ->
        %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}

      nil ->
        nil
    end
  end

  defp sentence_case(<<first::utf8, rest::binary>>),
    do: String.upcase(<<first::utf8>>) <> rest

  defp sentence_case(""), do: "Revise this expression"

  defp title(%ExpectationOrigin{kind: :annotation}), do: "Annotation does not match"
  defp title(%ExpectationOrigin{kind: :local_fact}), do: "Local fact does not match"
  defp title(%ExpectationOrigin{kind: :call_result}), do: "Call result has the wrong type"
  defp title(%ExpectationOrigin{kind: :branch}), do: "Branches have different types"
  defp title(%ExpectationOrigin{kind: :dependent_branch}), do: "Dependent branch has the wrong type"
  defp title(%ExpectationOrigin{kind: :condition}), do: "Condition is not boolean"
  defp title(%ExpectationOrigin{kind: :call_argument}), do: "Argument has the wrong type"
  defp title(%ExpectationOrigin{kind: :application}), do: "Application has the wrong type"
  defp title(%ExpectationOrigin{kind: :overload}), do: "No matching overload"
  defp title(%ExpectationOrigin{kind: :element}), do: "Collection element has the wrong type"
  defp title(%ExpectationOrigin{kind: :collection}), do: "Collection elements have different types"
  defp title(%ExpectationOrigin{kind: :record}), do: "Record has the wrong type"
  defp title(%ExpectationOrigin{kind: :record_field}), do: "Record field has the wrong type"
  defp title(%ExpectationOrigin{kind: :record_update}), do: "Record update has the wrong type"
  defp title(%ExpectationOrigin{kind: :pattern}), do: "Pattern has the wrong type"
  defp title(%ExpectationOrigin{kind: :constructor_argument}), do: "Constructor argument has the wrong type"
  defp title(%ExpectationOrigin{kind: :implicit}), do: "Implicit argument has the wrong type"
  defp title(%ExpectationOrigin{kind: :effects}), do: "Effect is not allowed here"
  defp title(%ExpectationOrigin{kind: :ffi}), do: "FFI boundary has the wrong type"
  defp title(%ExpectationOrigin{kind: :actor}), do: "Actor message has the wrong type"
  defp title(%ExpectationOrigin{kind: :fsm}), do: "FSM transition has the wrong type"
  defp title(%ExpectationOrigin{kind: :supervisor}), do: "Supervisor value has the wrong type"
  defp title(%ExpectationOrigin{kind: :operator_operand}), do: "Operator cannot use this value"
  defp title(_origin), do: "Type mismatch"

  defp context(%ExpectationOrigin{kind: :annotation}),
    do: "This expression does not match the type written in its annotation."

  defp context(%ExpectationOrigin{kind: :local_fact, owner: owner}),
    do: "The evidence for local fact `#{name(owner)}` does not match its stated type."

  defp context(%ExpectationOrigin{kind: :call_result, owner: owner}),
    do: "The result of `#{name(owner || "this call")}` does not match the surrounding expectation."

  defp context(%ExpectationOrigin{kind: :branch}),
    do: "Every branch of this expression must produce the same type."

  defp context(%ExpectationOrigin{kind: :dependent_branch}),
    do: "The constructor specializes this branch's indices, and its body must produce that refined result type."

  defp context(%ExpectationOrigin{kind: :condition}),
    do: "A condition must produce `Bool` before either branch can run."

  defp context(%ExpectationOrigin{kind: :call_argument, index: index, owner: owner}),
    do: "Argument #{display_index(index)} of `#{name(owner || "this function")}` has an incompatible type."

  defp context(%ExpectationOrigin{kind: :application, owner: owner}),
    do: "This application of `#{name(owner || "this function")}` has an incompatible type."

  defp context(%ExpectationOrigin{kind: :overload, owner: owner}),
    do: "The overloaded call `#{name(owner || "this function")}` has no compatible type."

  defp context(%ExpectationOrigin{kind: :operator_operand, owner: owner}),
    do: "The `#{name(owner || "operator")}` operator cannot use this operand type."

  defp context(%ExpectationOrigin{kind: :element, index: index}),
    do: "Element #{display_index(index)} of this collection has an incompatible type."

  defp context(%ExpectationOrigin{kind: :collection}),
    do: "All elements of this collection must agree on one type."

  defp context(%ExpectationOrigin{kind: :record, owner: owner}),
    do: "This value does not match the declared shape of record `#{name(owner || "this record")}`."

  defp context(%ExpectationOrigin{kind: :record_field, owner: owner}),
    do: "Field `#{name(owner || "this field")}` does not match the record's declared field type."

  defp context(%ExpectationOrigin{kind: :record_update, owner: owner}),
    do: "This record update does not preserve the declared record shape of `#{name(owner || "this record")}`."

  defp context(%ExpectationOrigin{kind: :pattern}),
    do: "This pattern must match the type of the value it is checking."

  defp context(%ExpectationOrigin{kind: :constructor_argument, index: index, owner: owner}),
    do:
      "Argument #{display_index(index)} of constructor `#{name(owner || "this constructor")}` has an incompatible type."

  defp context(%ExpectationOrigin{kind: :implicit, owner: owner}),
    do: "The implicit argument required by `#{name(owner || "this call")}` has the wrong type."

  defp context(%ExpectationOrigin{kind: :effects}),
    do: "This expression performs an effect that is not allowed in its context."

  defp context(%ExpectationOrigin{kind: :ffi, owner: owner}),
    do: "The FFI boundary `#{name(owner || "this declaration")}` does not match its Cure type."

  defp context(%ExpectationOrigin{kind: :actor, owner: owner}),
    do: "Actor `#{name(owner || "this actor")}` received a value with the wrong message type."

  defp context(%ExpectationOrigin{kind: :fsm, owner: owner}),
    do: "FSM transition `#{name(owner || "this transition")}` does not produce the required state type."

  defp context(%ExpectationOrigin{kind: :supervisor, owner: owner}),
    do: "Supervisor `#{name(owner || "this supervisor")}` does not match the required child specification type."

  defp context(_origin), do: "This expression has a different type than its context requires."

  defp label(%ExpectationOrigin{kind: :condition}), do: "this condition has the wrong type"
  defp label(%ExpectationOrigin{kind: :local_fact}), do: "this evidence has the wrong type"
  defp label(%ExpectationOrigin{kind: :call_result}), do: "this call result has the wrong type"
  defp label(%ExpectationOrigin{kind: :branch}), do: "this branch disagrees with another branch"
  defp label(%ExpectationOrigin{kind: :dependent_branch}), do: "this branch does not satisfy its refined result"
  defp label(%ExpectationOrigin{kind: :call_argument}), do: "this argument has the wrong type"
  defp label(%ExpectationOrigin{kind: :application}), do: "this application has the wrong type"
  defp label(%ExpectationOrigin{kind: :overload}), do: "this overloaded call has no matching type"
  defp label(%ExpectationOrigin{kind: :element}), do: "this collection element has the wrong type"
  defp label(%ExpectationOrigin{kind: :collection}), do: "this collection element has the wrong type"
  defp label(%ExpectationOrigin{kind: :record}), do: "this record has the wrong type"
  defp label(%ExpectationOrigin{kind: :record_field}), do: "this record field has the wrong type"
  defp label(%ExpectationOrigin{kind: :record_update}), do: "this record update has the wrong type"
  defp label(%ExpectationOrigin{kind: :pattern}), do: "this pattern has the wrong type"
  defp label(%ExpectationOrigin{kind: :constructor_argument}), do: "this constructor argument has the wrong type"
  defp label(%ExpectationOrigin{kind: :implicit}), do: "this implicit argument has the wrong type"
  defp label(%ExpectationOrigin{kind: :effects}), do: "this expression has an invalid effect"
  defp label(%ExpectationOrigin{kind: :ffi}), do: "this FFI boundary has the wrong type"
  defp label(%ExpectationOrigin{kind: :actor}), do: "this actor message has the wrong type"
  defp label(%ExpectationOrigin{kind: :fsm}), do: "this FSM transition has the wrong type"
  defp label(%ExpectationOrigin{kind: :supervisor}), do: "this supervisor value has the wrong type"
  defp label(%ExpectationOrigin{kind: :operator_operand}), do: "this operator operand has the wrong type"
  defp label(_origin), do: "this expression has the wrong type"

  defp expectation_labels(%ExpectationOrigin{span: %Span{} = span}, primary_span, _related)
       when span != primary_span,
       do: [%Label{span: span, style: :secondary, message: "the expectation comes from here"}]

  defp expectation_labels(_origin, primary_span, %Span{} = related) when related != primary_span,
    do: [%Label{span: related, style: :secondary, message: "the compared expression is here"}]

  defp expectation_labels(_origin, _primary_span, _related), do: []

  defp display_index(nil), do: ""
  defp display_index(index), do: index + 1

  defp name(value) when is_atom(value), do: Atom.to_string(value)
  defp name(value) when is_binary(value), do: value
  defp name(value), do: inspect(value)
end
