defmodule Cure.Diagnostic.Adapter do
  @moduledoc "Converts phase-specific and legacy error values into shared diagnostics."

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    ExpectationOrigin,
    Label,
    ProvenanceFrame,
    Span,
    Suggestion,
    SyntaxProblem,
    TextEdit,
    TypeProblem
  }

  @unknown_name_code "E091"

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:error, reason}, opts), do: from_error(reason, opts)

  def from_error({:type_error, errors}, opts) when is_list(errors) do
    from_error(errors, opts)
  end

  def from_error([reason | _], opts), do: from_error(reason, opts)

  def from_error([], opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Type mismatch",
      body: Doc.paragraph("The type checker reported an unsatisfied constraint without further detail."),
      primary: primary_label(opts, "this expression does not satisfy its type constraints"),
      payload: %{errors: []}
    )
  end

  def from_error({:type_mismatch, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Type mismatch",
      body: Doc.paragraph(message),
      primary: primary_label(opts, "this expression has the wrong type"),
      payload: %{message: message, meta: meta}
    )
  end

  def from_error({:unknown_erasure_class, name, class}, opts) do
    erasure_failure(:unknown_erasure_class, %{name: name, class: class}, opts)
  end

  def from_error({:erases_on_non_opaque, name}, opts) do
    erasure_failure(:erases_on_non_opaque, %{name: name}, opts)
  end

  def from_error({:non_strictly_positive, family}, opts) do
    Diagnostic.new(
      code: "E103",
      key: :non_strictly_positive_type,
      severity: :error,
      title: "Non-strictly-positive type",
      body:
        Doc.paragraph(
          "The recursive occurrence in `#{name_to_string(family)}` is not strictly positive, so this type cannot be accepted by the normalising kernel."
        ),
      primary: primary_label(opts, "this recursive type definition is not strictly positive"),
      payload: %{family: family}
    )
  end

  def from_error({:erased_used_relevantly, details}, opts) when is_map(details) do
    site = Map.get(details, :site, :runtime)
    binder = Map.get(details, :binder)

    Diagnostic.new(
      code: "E104",
      key: :erased_value_used_relevantly,
      severity: :error,
      title: "Erased value used relevantly",
      body:
        Doc.paragraph(
          "An erased value#{if is_nil(binder), do: "", else: " (binder #{binder})"} is used in the runtime-relevant `#{site}` position."
        ),
      primary: primary_label(opts, "remove this runtime use or make the binding relevant"),
      payload: details
    )
  end

  def from_error({:usage_violation, details}, opts) when is_map(details) do
    declared = Map.get(details, :declared, :unknown)
    used = Map.get(details, :used, :unknown)
    binder = Map.get(details, :binder)

    Diagnostic.new(
      code: "E104",
      key: :erased_value_used_relevantly,
      severity: :error,
      title: "Resource usage violates its grade",
      body:
        Doc.paragraph(
          "This #{if is_nil(binder), do: "binding", else: "binder #{binder}"} is declared `#{declared}` but used as `#{used}`. Restricted resources must not be duplicated or consumed at an incompatible grade."
        ),
      primary: primary_label(opts, "use this binding according to its declared grade"),
      payload: details
    )
  end

  def from_error({kind, name}, opts)
      when kind in [
             :duplicate_type,
             :duplicate_ctor,
             :duplicate_field,
             :duplicate_parameter,
             :reserved_union_type_name,
             :constructor_function_collision,
             :duplicate_definition
           ] do
    declaration_conflict(kind, %{name: name}, opts)
  end

  def from_error({:overlapping_overload, name, arity}, opts) do
    declaration_conflict(:overlapping_overload, %{name: name, arity: arity}, opts)
  end

  def from_error({:overlapping_instance, interface, head}, opts) do
    declaration_conflict(:overlapping_instance, %{interface: interface, head: head}, opts)
  end

  def from_error({:overlapping_named_instance, name, interface, head}, opts) do
    declaration_conflict(
      :overlapping_named_instance,
      %{name: name, interface: interface, head: head},
      opts
    )
  end

  def from_error({:sibling_module_collision, name, owners}, opts) do
    declaration_conflict(:sibling_module_collision, %{name: name, owners: owners}, opts)
  end

  def from_error({:precedence_cycle, groups}, opts) do
    operator_conflict(:precedence_cycle, %{groups: groups}, opts)
  end

  def from_error({:builtin_operator_not_overloadable, operator}, opts) do
    operator_conflict(:builtin_operator_not_overloadable, %{operator: operator}, opts)
  end

  def from_error({:unsupported_operand_type, operator}, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Operator operand type mismatch",
      body: Doc.paragraph("The operands of `#{name_to_string(operator)}` do not have a supported type combination."),
      primary: primary_label(opts, "change the operand types or use a supported operator"),
      payload: %{kind: :unsupported_operand_type, operator: operator}
    )
  end

  def from_error({:no_operator_meaning, operator}, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Operator has no valid meaning",
      body:
        Doc.paragraph(
          "The operator `#{name_to_string(operator)}` has no valid meaning for the surrounding operand types."
        ),
      primary: primary_label(opts, "use an operator supported by these types"),
      payload: %{kind: :no_operator_meaning, operator: operator}
    )
  end

  def from_error({:cannot_infer_match_type, expression}, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Cannot infer match type",
      body: Doc.paragraph("The compiler cannot determine one common type for the branches of this match expression."),
      primary: primary_label(opts, "add an annotation or make the branches agree"),
      payload: %{kind: :cannot_infer_match_type, expression: expression}
    )
  end

  def from_error({:lambda_expected_pi, expected}, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Lambda used where a function was not expected",
      body:
        Doc.paragraph(
          "This lambda can only be checked against a function type, but the expected type is `#{surface_type(expected)}`."
        ),
      primary: primary_label(opts, "change the expected type or remove this lambda"),
      payload: %{kind: :lambda_expected_pi, expected: expected}
    )
  end

  def from_error({:unsupported_async, message, meta}, opts)
      when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E107",
      key: :unsupported_async,
      severity: :error,
      title: "Unsupported asynchronous primitive",
      body: Doc.paragraph(message),
      primary: primary_label(opts, "use a supported asynchronous boundary"),
      payload: %{message: message, meta: meta}
    )
  end

  def from_error({:splice_outside_quote, tag, meta}, opts) when is_list(meta) do
    form = if tag == :splice_group, do: "$(e ...)", else: "$(e)"

    Diagnostic.new(
      code: "E108",
      key: :splice_outside_quote,
      severity: :error,
      title: "Splice outside quote",
      body: Doc.paragraph("The `#{form}` splice has no surrounding quote to receive generated syntax."),
      primary: primary_label(opts, "place this splice inside a quote"),
      payload: %{tag: tag, meta: meta}
    )
  end

  def from_error({:missing_diagnosis, points}, opts), do: macro_validation_failure(:missing_diagnosis, points, opts)
  def from_error({:rule_unpinned, keywords}, opts), do: macro_validation_failure(:rule_unpinned, keywords, opts)

  def from_error({:example_mismatch, mismatches}, opts),
    do: macro_validation_failure(:example_mismatch, mismatches, opts)

  def from_error({:example_type_mismatch, failures}, opts),
    do: macro_validation_failure(:example_type_mismatch, failures, opts)

  def from_error({:computed_example_error, failures}, opts),
    do: macro_validation_failure(:computed_example_error, failures, opts)

  def from_error({:codegen_error, {:computed_macro_error, _, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {:expansion_ill_typed, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_global, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_global, _, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_name, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unknown_constructor, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:conversion_failure, _, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:source_context, _, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:unfilled_hole, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, reason}, opts), do: codegen_failure(reason, opts)

  def from_error({:parse_error, [reason | _]}, opts), do: from_error(reason, opts)

  def from_error({:source_context, {:unsupported_pattern, shape}, context}, opts) when is_map(context) do
    from_error(
      %SyntaxProblem{
        kind: :unrecognized_pattern,
        observed: shape,
        at: Keyword.get(opts, :span, Map.get(context, :span)),
        context: %{code: "E090", checking: Map.get(context, :checking)}
      },
      opts
    )
  end

  def from_error({:source_context, {:unsolved_metavariables, name}, context}, opts) when is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "Missing implicit argument",
      body: Doc.paragraph("Cure could not infer every implicit argument for `#{name}` at this call site."),
      primary: primary_label(opts, "the implicit argument cannot be inferred"),
      payload: %{
        name: name,
        checking: Map.get(context, :checking),
        expectation_origin: Map.get(context, :expectation_origin)
      }
    )
  end

  def from_error({:source_context, {:no_instance, interface, head}, context}, opts)
      when is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))
    origin = Map.get(context, :expectation_origin, :implicit)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "No instance found",
      body:
        Doc.stack([
          Doc.paragraph(
            "Cure could not find an implementation of `#{name_to_string(interface)}` for the required type `#{surface_type(head)}`."
          ),
          Doc.paragraph("Add an instance, import the module that provides it, or change the expression's type.")
        ]),
      primary: primary_label(opts, "this implicit constraint has no available instance"),
      payload: %{
        kind: :no_instance,
        interface: interface,
        head: head,
        expectation_origin: origin,
        checking: Map.get(context, :checking)
      }
    )
  end

  def from_error({:source_context, {:no_named_instance, name}, context}, opts) when is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "Named instance not found",
      body: Doc.paragraph("The named instance `#{name_to_string(name)}` is not available in this scope."),
      primary: primary_label(opts, "import or define this named instance"),
      payload: %{kind: :no_named_instance, name: name, checking: Map.get(context, :checking)}
    )
  end

  def from_error({:source_context, {:missing_branch, branch}, context}, opts) when is_map(context) do
    coverage_problem(:missing_branch, branch, context, opts)
  end

  def from_error({:source_context, {:reachable_impossible, branch}, context}, opts) when is_map(context) do
    coverage_problem(:reachable_impossible, branch, context, opts)
  end

  def from_error({:source_context, {:duplicate_branch, branch}, context}, opts) when is_map(context) do
    coverage_problem(:duplicate_branch, branch, context, opts)
  end

  def from_error({:source_context, {:forced_pattern_mismatch, actual, expected}, context}, opts)
      when is_map(context) do
    pattern_problem(:forced_pattern_mismatch, %{actual: actual, expected: expected}, context, opts)
  end

  def from_error({:source_context, {:named_implicit_unforced, name}, context}, opts) when is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "Named implicit was not forced",
      body: Doc.paragraph("The named implicit `#{name_to_string(name)}` must be explicitly forced in this pattern."),
      primary: primary_label(opts, "force this named implicit or remove the pattern reference"),
      payload: %{kind: :named_implicit_unforced, name: name, checking: Map.get(context, :checking)}
    )
  end

  def from_error({:source_context, {kind, first, second}, context}, opts)
      when kind in [:with_rematch_ctor_mismatch] and is_map(context) do
    pattern_problem(kind, %{actual: first, expected: second}, context, opts)
  end

  def from_error({:source_context, {kind, details}, context}, opts)
      when kind in [
             :with_rematch_ctor_mismatch,
             :with_rematch_non_constructor_pattern,
             :with_rematch_inconsistent_binding
           ] and
             is_map(context) do
    pattern_problem(kind, %{details: details}, context, opts)
  end

  def from_error({:source_context, {:unknown_record, name}, context}, opts) when is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    Diagnostic.new(
      code: "E021",
      key: :unknown_record,
      severity: :error,
      title: "Unknown record",
      body: Doc.paragraph("The record `#{name}` is not declared in this module or its imports."),
      primary: primary_label(opts, "declare this record before constructing it"),
      payload: %{record: name, checking: Map.get(context, :checking)}
    )
  end

  def from_error({:source_context, {:unknown_field, record, field}, context}, opts) when is_map(context) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(context, :span))
      |> Keyword.put(:owner, record)
      |> Keyword.put(:checking, Map.get(context, :checking))

    unknown_name(:member, "#{name_to_string(record)}.#{name_to_string(field)}", opts)
  end

  def from_error({:unknown_field, record, field}, opts) do
    unknown_name(:member, "#{name_to_string(record)}.#{name_to_string(field)}", Keyword.put(opts, :owner, record))
  end

  def from_error({:source_context, {:projection_non_record, field}, context}, opts) when is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Record projection requires a record",
      body: Doc.paragraph("The value being projected with `#{name_to_string(field)}` is not a record."),
      primary: primary_label(opts, "project a field from a record value"),
      payload: %{kind: :projection_non_record, field: field, checking: Map.get(context, :checking)}
    )
  end

  def from_error({:unknown_record, name}, opts),
    do: from_error({:source_context, {:unknown_record, name}, %{}}, opts)

  def from_error({:source_context, {:record_field_mismatch, name}, context}, opts) when is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    Diagnostic.new(
      code: "E022",
      key: :record_field_mismatch,
      severity: :error,
      title: "Record field mismatch",
      body: Doc.paragraph("The fields supplied to `#{name}` do not match its declared record shape."),
      primary: primary_label(opts, "use exactly the declared record fields"),
      payload: %{record: name, checking: Map.get(context, :checking)}
    )
  end

  def from_error({:source_context, {kind, name}, context}, opts)
      when kind in [:unknown_ctor, :foreign_ctor, :unknown_pattern_constructor, :unknown_family] and
             is_map(context) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))
    namespace = if kind == :unknown_family, do: :type, else: :constructor
    unknown_name(namespace, name, Keyword.put(opts, :checking, Map.get(context, :checking)))
  end

  def from_error({:source_context, reason, context}, opts) when is_map(context) do
    opts =
      opts
      |> Keyword.put(:checking, Map.get(context, :checking))
      |> then(fn opts ->
        case Map.get(context, :span) do
          # A presentation boundary may have remapped this span into its own
          # source registry (for example `Errors.to_diagnostic/3`). Preserve
          # that registry-owned span instead of restoring the compiler's
          # original `nofile` identity.
          %Span{} = span -> Keyword.put_new(opts, :span, span)
          _ -> opts
        end
      end)

    case {reason, Map.get(context, :expectation_origin)} do
      {{:conversion_failure, actual, expected}, origin} when not is_nil(origin) ->
        from_error(
          %TypeProblem{
            kind: :conversion_failure,
            actual: actual,
            expected: expected,
            origin: %ExpectationOrigin{
              kind: origin,
              span: Map.get(context, :expectation_span),
              owner: Map.get(context, :checking)
            },
            expression: Map.get(context, :expression_category, :expression),
            span: Keyword.get(opts, :span, Map.get(context, :span)),
            debug: %{cause: reason, checking: Map.get(context, :checking)}
          },
          opts
        )

      _ ->
        from_error(reason, opts)
    end
  end

  def from_error({:unknown_global, name}, opts),
    do: unknown_name(:value, name, opts)

  def from_error({:unknown_global, name, details}, opts) when is_map(details),
    do: unknown_name(:value, name, Keyword.put(opts, :kernel_context, details))

  def from_error({:unknown_name, details}, opts) when is_map(details) do
    namespace = Map.get(details, :namespace, :value)
    name = Map.get(details, :name, "<unknown>")

    unknown_name(
      namespace,
      name,
      opts
      |> Keyword.put(:candidates, Map.get(details, :candidates, []))
      |> Keyword.put(:owner, Map.get(details, :owner))
      |> Keyword.put(:checking, Map.get(details, :checking))
      |> Keyword.put(:arity, Map.get(details, :arity))
      |> Keyword.put(:expected_namespace, Map.get(details, :expected_namespace))
      |> Keyword.put(:imported_from, Map.get(details, :imported_from))
      |> Keyword.put(:span, Map.get(details, :span))
      |> Keyword.put(:provenance, Map.get(details, :provenance, []))
    )
  end

  def from_error({:unknown_constructor, name}, opts),
    do: unknown_name(:constructor, name, opts)

  def from_error({:unknown_type, name}, opts),
    do: unknown_name(:type, name, opts)

  def from_error({:unknown_module, name}, opts),
    do: unknown_name(:module, name, opts)

  def from_error({:unknown_member, module, name}, opts),
    do: unknown_name(:member, "#{module}.#{name}", Keyword.put(opts, :owner, module))

  def from_error({:unbound_variable, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E002",
      key: :unbound_variable,
      severity: :error,
      title: "Unbound variable",
      message: message,
      primary: primary_label(opts, "this variable is not bound here"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:unfilled_hole, name}, opts) do
    Diagnostic.new(
      code: "E014",
      key: :unfilled_hole,
      severity: :error,
      title: "Unfilled hole",
      body: Doc.paragraph("The compiler reached the unfinished hole `?#{name}`."),
      primary: primary_label(opts, "replace this hole with an expression"),
      payload: %{name: name}
    )
  end

  def from_error({:arity_mismatch, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Arity mismatch",
      message: message,
      primary: primary_label(opts, "the number of arguments does not match"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:extern_arity_mismatch, name, declared, present}, opts)
      when is_integer(declared) and is_integer(present) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Arity mismatch",
      body:
        Doc.paragraph(
          "Extern `#{name_to_string(name)}` declares target arity #{declared}, but its present Cure arity is #{present}."
        ),
      primary: primary_label(opts, "make the extern declaration match its callable arity"),
      payload: %{name: name_to_string(name), declared: declared, present: present, kind: :extern}
    )
  end

  def from_error({:constructor_arity_mismatch, name}, opts) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Constructor arity mismatch",
      body: Doc.paragraph("Constructor `#{name_to_string(name)}` was used with the wrong number of arguments."),
      primary: primary_label(opts, "provide the arguments required by this constructor"),
      payload: %{kind: :constructor, constructor: name_to_string(name)}
    )
  end

  def from_error({:tuple_arity_mismatch, direction, details}, opts) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Tuple arity mismatch",
      body: Doc.paragraph("This tuple pattern has the wrong number of elements (#{direction})."),
      primary: primary_label(opts, "make the tuple pattern match the value's arity"),
      payload: %{kind: :tuple, direction: direction, details: details}
    )
  end

  def from_error({:with_rematch_arity_mismatch, expected, actual}, opts) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "With-pattern arity mismatch",
      body: Doc.paragraph("The original `with` match has #{expected} pattern(s), but its rematch has #{actual}."),
      primary: primary_label(opts, "keep the rematched patterns aligned with the original values"),
      payload: %{kind: :with_rematch, expected: expected, actual: actual}
    )
  end

  def from_error({:typed_pattern_type_mismatch, type_ast}, opts) do
    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Pattern annotation does not match",
      body: Doc.paragraph("This pattern's annotation is incompatible with the value it matches."),
      primary: primary_label(opts, "change the pattern or its type annotation"),
      payload: %{kind: :typed_pattern, annotation: type_ast}
    )
  end

  def from_error({:extern_untyped_head, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E056",
      key: :extern_untyped_head,
      severity: :error,
      title: "@extern declaration missing a typed head",
      message: message,
      primary: primary_label(opts, "add parameter and return type annotations"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:extern_has_body, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E057",
      key: :extern_has_body,
      severity: :error,
      title: "@extern declaration has a body",
      message: message,
      primary: primary_label(opts, "remove the body from this extern declaration"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:proof_shape_mismatch, message, name}, opts) when is_binary(message) do
    Diagnostic.new(
      code: "E026",
      key: :proof_shape_mismatch,
      severity: :error,
      title: "Proof shape mismatch",
      message: message,
      primary: primary_label(opts, "return a propositional equality from this proof binding"),
      payload: %{name: name}
    )
  end

  def from_error({:ambiguous_proof_search, goal, candidates}, opts) when is_list(candidates) do
    Diagnostic.new(
      code: "E026",
      key: :proof_shape_mismatch,
      severity: :error,
      title: "Proof search is ambiguous",
      body:
        Doc.paragraph(
          "More than one proof can solve the current obligation, so the compiler cannot choose a deterministic witness."
        ),
      primary: primary_label(opts, "make the proof obligation unambiguous"),
      payload: %{kind: :ambiguous_proof_search, goal: goal, candidates: candidates}
    )
  end

  def from_error({:totality_required, name}, opts) do
    Diagnostic.new(
      code: "E013",
      key: :totality_failure,
      severity: :error,
      title: "Totality failure",
      body: Doc.paragraph("`#{name}` must be total because it is used during type-level computation."),
      primary: primary_label(opts, "make this definition structurally total"),
      payload: %{name: name}
    )
  end

  def from_error({:compile_time_totality, name, reason}, opts) do
    diagnostic = from_error({:totality_required, name}, opts)
    %{diagnostic | payload: Map.put(diagnostic.payload, :reason, inspect(reason))}
  end

  def from_error({kind, message, meta}, opts)
      when kind in [:pickup_no_else, :pickup_else_not_last, :pickup_multiple_else] and
             is_binary(message) and is_list(meta) do
    {code, key, title, hint} =
      case kind do
        :pickup_no_else ->
          {"E076", :pickup_missing_else, "pickup without else", "add a final `else -> ...` clause"}

        :pickup_else_not_last ->
          {"E077", :pickup_else_not_last, "pickup else is not last", "move `else -> ...` to the final clause"}

        :pickup_multiple_else ->
          {"E078", :pickup_multiple_else, "pickup has multiple else clauses", "keep exactly one `else -> ...` clause"}
      end

    Diagnostic.new(
      code: code,
      key: key,
      severity: :error,
      title: title,
      message: message,
      primary: primary_label(opts, hint),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:ambiguous_name, name, modules}, opts) when is_list(modules) do
    spelling = name_to_string(name)
    owners = Enum.map(modules, &name_to_string/1)

    Diagnostic.new(
      code: "E089",
      key: :ambiguous_name,
      severity: :error,
      title: "Ambiguous name",
      message: "`#{spelling}` is provided by more than one imported module.",
      primary: primary_label(opts, "qualification is required here"),
      suggestions: [
        %Suggestion{
          message: "Qualify the name as #{Enum.map_join(owners, " or ", &"`#{&1}.#{spelling}`")}",
          applicability: :manual
        }
      ],
      payload: %{namespace: :value, name: spelling, owners: owners}
    )
  end

  def from_error({:duplicate_module, name, paths}, opts) when is_list(paths) do
    Diagnostic.new(
      code: "E087",
      key: :duplicate_module,
      severity: :error,
      title: "Duplicate module",
      message: "Module `#{name_to_string(name)}` is declared by more than one file: #{Enum.join(paths, ", ")}.",
      primary: primary_label(opts, "one declaration is here"),
      payload: %{module: name_to_string(name), paths: paths}
    )
  end

  def from_error({:duplicate_module_identity, name, other_path, path}, opts) do
    from_error({:duplicate_module, name, [other_path, path]}, opts)
  end

  def from_error({:duplicate_module_identity, name, paths}, opts) when is_list(paths) do
    from_error({:duplicate_module, name, paths}, opts)
  end

  def from_error({:import_cycle, hops}, opts) when is_list(hops) do
    chain = Enum.map_join(hops, " -> ", fn hop -> "#{hop.module} (#{hop.path}:#{hop.line})" end)

    Diagnostic.new(
      code: "W086",
      key: :import_cycle,
      severity: :warning,
      title: "Import cycle",
      message: "This warning means the modules form a `use` cycle: #{chain}.",
      primary: primary_label(opts, "the cycle begins here"),
      notes: ["Cycle members compile together in deterministic order; qualify cross-module calls when order matters."],
      payload: %{hops: hops}
    )
  end

  def from_error({:unresolved_import, name, arity, imports, line}, opts) when is_list(imports) do
    spelling = name_to_string(name)
    modules = Enum.map(imports, &name_to_string/1)

    Diagnostic.new(
      code: "W088",
      key: :unresolved_import,
      severity: :warning,
      title: "Unresolved import",
      message: "This warning means `#{spelling}/#{arity}` matches no export of #{Enum.join(modules, ", ")}.",
      primary: primary_label(opts, "this call falls back to a local call"),
      suggestions: [
        %Suggestion{message: "Qualify the call with the module that defines it", applicability: :manual}
      ],
      payload: %{name: spelling, arity: arity, imports: modules, line: line}
    )
  end

  def from_error(%TypeProblem{} = problem, opts) do
    actual_surface = surface_type(problem.actual)
    expected_surface = surface_type(problem.expected)
    primary_span = problem.span || Keyword.get(opts, :span)

    primary =
      if primary_span do
        %Label{span: primary_span, style: :primary, message: type_problem_label(problem.origin)}
      end

    secondary = expectation_labels(problem.origin, primary_span, problem.related)

    Diagnostic.new(
      code: "E093",
      key: problem.kind,
      severity: :error,
      title: type_problem_title(problem.origin),
      body:
        Doc.stack([
          Doc.paragraph(type_problem_context(problem.origin)),
          type_comparison_doc(problem.expected, problem.actual)
        ]),
      primary: primary,
      secondary: secondary,
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        expected_surface: expected_surface,
        actual_surface: actual_surface,
        origin: Map.from_struct(problem.origin),
        expression_category: problem.expression,
        expected_core: inspect(problem.expected),
        actual_core: inspect(problem.actual),
        debug: problem.debug
      }
    )
  end

  def from_error(%SyntaxProblem{} = problem, opts) do
    span = problem.at || Keyword.get(opts, :span)
    code = Map.get(problem.context, :code, "E094")

    primary =
      if span do
        %Label{span: span, style: :primary, message: syntax_problem_label(problem)}
      end

    Diagnostic.new(
      code: code,
      key: problem.kind,
      severity: :error,
      title: syntax_problem_title(problem),
      body:
        Doc.stack([
          Doc.paragraph(syntax_problem_context(problem)),
          syntax_expected_doc(problem)
        ]),
      primary: primary,
      secondary: syntax_secondary_labels(problem, span),
      suggestions: syntax_insertions(problem, span),
      payload: %{
        kind: problem.kind,
        expected: problem.expected,
        alternatives: problem.alternatives,
        observed: problem.observed,
        at: problem.at,
        within: problem.within,
        opener: problem.opener,
        previous: problem.previous,
        context: problem.context
      }
    )
  end

  def from_error({:conversion_failure, actual, expected}, opts) do
    actual_surface = print_core(actual)
    expected_surface = print_core(expected)

    Diagnostic.new(
      code: "E093",
      key: :conversion_failure,
      severity: :error,
      title: "Type mismatch",
      body: type_comparison_doc(expected, actual),
      primary: primary_label(opts, "this expression has the wrong type"),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        expected_surface: expected_surface,
        actual_surface: actual_surface,
        expected_core: inspect(expected),
        actual_core: inspect(actual)
      }
    )
  end

  def from_error({:expected, expected, :got, actual, line, column}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :unexpected_token,
        expected: expected,
        observed: actual,
        at: Keyword.get(opts, :span),
        context: %{line: line, column: column}
      },
      opts
    )
  end

  def from_error({:expected_token, expected, actual_type, actual_value, line, column}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :unexpected_token,
        expected: expected,
        observed: if(is_nil(actual_value), do: actual_type, else: actual_value),
        at: Keyword.get(opts, :span),
        context: %{line: line, column: column, token_type: actual_type}
      },
      opts
    )
  end

  def from_error({:unexpected_token, actual, line, column}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :unexpected_token,
        observed: actual,
        at: Keyword.get(opts, :span),
        context: %{line: line, column: column}
      },
      opts
    )
  end

  def from_error({:parse_recovered, actual, line, column}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :recovered_statement,
        observed: actual,
        at: Keyword.get(opts, :span),
        context: %{line: line, column: column, code: "E063"}
      },
      opts
    )
  end

  def from_error({:lambda_block_unterminated, line, column, code}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :unterminated_lambda,
        expected: :rbrace,
        observed: :eof,
        at: Keyword.get(opts, :span),
        context: %{line: line, column: column, code: code}
      },
      opts
    )
  end

  def from_error({:lex_error, reason}, opts), do: from_error(lex_problem(reason, opts), opts)

  def from_error({:macro_use_mismatch, keyword, expected, got, _line, _column}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :macro_use_mismatch,
        expected: expected,
        observed: got,
        at: Keyword.get(opts, :span),
        alternatives: [],
        context: %{keyword: keyword}
      },
      opts
    )
  end

  def from_error({:malformed_hole, _line, _column}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :malformed_macro_hole,
        expected: :macro_hole,
        observed: :eof,
        at: Keyword.get(opts, :span),
        context: %{repair: "<name: Kind>"}
      },
      opts
    )
  end

  def from_error({kind, line, column}, opts)
      when kind in [:edition_pragma_placement, :edition_pragma_malformed, :edition_pragma_unknown] and
             is_integer(line) and is_integer(column) do
    from_error(
      %SyntaxProblem{
        kind: kind,
        observed: :edition_pragma,
        at: Keyword.get(opts, :span),
        context: %{column: column}
      },
      opts
    )
  end

  def from_error({:edition_error, {:unknown_edition, edition}}, opts) do
    Diagnostic.new(
      code: "E094",
      key: :edition_pragma_unknown,
      severity: :error,
      title: "Unknown edition",
      body: Doc.paragraph("The edition `#{edition}` is not supported. Use edition `#{Cure.Edition.current()}`."),
      primary: primary_label(opts, "choose a supported edition"),
      payload: %{edition: edition, current: Cure.Edition.current()}
    )
  end

  def from_error({:computed_macro_error, meta, reason}, opts) when is_list(meta) do
    keyword = Keyword.get(meta, :keyword, "computed")

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "Computed macro expansion failed",
      body:
        Doc.paragraph(
          "The `#{keyword}` computed macro could not produce valid Cure syntax: #{computed_macro_reason(reason)}"
        ),
      primary: primary_label(opts, "this macro invocation generated the failing syntax"),
      notes: ["Edit the authored macro invocation or its rule; generated syntax is not the user-facing source."],
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{keyword: keyword, reason: inspect(reason)}
    )
  end

  def from_error({:macro_expansion_cycle, chain}, opts) when is_list(chain) do
    macro_expansion_failure(
      :cycle,
      "Macro expansion is recursive and did not reach a stable result.",
      chain,
      opts
    )
  end

  def from_error({:macro_expansion_budget, kind, frames}, opts) when is_atom(kind) and is_list(frames) do
    macro_expansion_failure(
      {:budget, kind},
      "Macro expansion exceeded its #{kind} limit.",
      frames,
      opts
    )
  end

  def from_error({:expansion_ill_typed, details}, opts) when is_map(details) do
    keyword = Map.get(details, :keyword, "computed")

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "Macro expansion proof failed",
      body: Doc.paragraph("The `#{keyword}` macro generated code that does not satisfy the dependent elaborator."),
      primary: primary_label(opts, "this macro invocation generated the invalid expansion"),
      notes: ["Edit the authored macro invocation; generated code is an implementation detail."],
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        keyword: keyword,
        input: Map.get(details, :input),
        expansion: Map.get(details, :expansion),
        reason: inspect(Map.get(details, :kernel_error) || Map.get(details, :reason))
      }
    )
  end

  def from_error({:beam_lint_error, errors, warnings}, opts) do
    codegen_failure({:beam_lint, errors, warnings}, opts)
  end

  def from_error({:beam_lint_error, errors}, opts) do
    codegen_failure({:beam_lint, errors}, opts)
  end

  def from_error({:final_core_violation, rejections}, opts) when is_list(rejections) do
    final_core_failure(nil, rejections, opts)
  end

  def from_error({:final_core_violation, name, rejections}, opts) when is_list(rejections) do
    final_core_failure(name, rejections, opts)
  end

  def from_error({:expected_module, _ast}, opts), do: codegen_failure(:expected_module, opts)
  def from_error({:unsupported_container, type}, opts), do: codegen_failure({:unsupported_container, type}, opts)

  def from_error({:lift_module_error, details}, opts) when is_map(details) do
    macro = get_in(details, [:source_provenance, :macro]) || :macro
    cause = Map.get(details, :cause)
    cause_diagnostic = from_error(cause)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "#{macro_title(macro)} expansion failed",
      message: macro_failure_message(macro, details.module, cause_diagnostic),
      primary: primary_label(opts, "this `#{macro}` declaration generated the failing module"),
      notes: ["The generated module is an implementation detail; edit the `#{macro}` declaration instead."],
      provenance: provenance_frames(details, opts),
      payload: %{
        macro: name_to_string(macro),
        module: name_to_string(details.module),
        behaviour: Map.get(details, :behaviour),
        cause: %{code: cause_diagnostic.code, key: cause_diagnostic.key, payload: cause_diagnostic.payload}
      }
    )
  end

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp macro_expansion_failure(kind, message, frames, opts) do
    provenance =
      frames
      |> Enum.filter(&is_map/1)
      |> Enum.map(fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword, "macro"),
          invocation: Keyword.get(opts, :span)
        }
      end)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: if(kind == :cycle, do: "Macro expansion cycle", else: "Macro expansion limit exceeded"),
      body: Doc.paragraph(message),
      primary: primary_label(opts, "reduce or stop this macro expansion"),
      provenance: provenance ++ Keyword.get(opts, :provenance, []),
      payload: %{kind: kind, frames: frames}
    )
  end

  defp codegen_failure(reason, opts) do
    {title, body, kind} = codegen_failure_content(reason)

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary_label(opts, "code generation failed here"),
      notes: ["This is an internal compiler failure; report it with the diagnostic fingerprint."],
      payload: %{kind: kind, debug_reason: inspect(reason)}
    )
  end

  defp codegen_failure_content(:expected_module) do
    {"Module emission failed", "The compiler expected a module definition before emitting a BEAM artifact.",
     :expected_module}
  end

  defp codegen_failure_content({:unsupported_container, type}) do
    {"Unsupported container", "The compiler cannot emit the `#{name_to_string(type)}` container in this context.",
     :unsupported_container}
  end

  defp codegen_failure_content({:beam_lint, errors, warnings}) when is_list(errors) and is_list(warnings) do
    {"BEAM validation failed",
     "The generated BEAM artifact was rejected by the BEAM validator (#{length(errors)} error(s), #{length(warnings)} warning(s)).",
     :beam_lint}
  end

  defp codegen_failure_content({:beam_lint, errors}) when is_list(errors) do
    {"BEAM validation failed",
     "The generated BEAM artifact was rejected by the BEAM validator (#{length(errors)} error(s)).", :beam_lint}
  end

  defp codegen_failure_content(_reason) do
    {"Code generation failed", "The compiler could not produce a valid BEAM artifact for this source.", :codegen}
  end

  defp final_core_failure(name, rejections, opts) do
    clauses = Enum.map(rejections, &Map.get(&1, :clause))
    messages = Enum.map(rejections, &Map.get(&1, :message))

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Final-Core validation failed",
      body:
        Doc.paragraph(
          "The compiler rejected an internal Core term at the trusted boundary (#{Enum.join(Enum.map(messages, &to_string/1), "; ")})."
        ),
      primary: primary_label(opts, "this definition produced invalid internal Core"),
      notes: ["This is an internal compiler failure; report it with the diagnostic fingerprint."],
      payload: %{kind: :final_core_violation, name: name, clauses: clauses, messages: messages}
    )
  end

  defp erasure_failure(kind, details, opts) do
    body =
      case kind do
        :unknown_erasure_class ->
          "`@erases(#{inspect(details.class)})` on `#{name_to_string(details.name)}` is not a supported erasure class. Supported classes: #{known_erasure_classes_hint()}."

        :erases_on_non_opaque ->
          "`#{name_to_string(details.name)}` has constructors, so its runtime erasure is already determined. `@erases` is only valid on a constructor-less opaque type."
      end

    Diagnostic.new(
      code: "E102",
      key: :erasure_violation,
      severity: :error,
      title: "Erasure violation",
      body: Doc.paragraph(body),
      primary: primary_label(opts, "this erasure declaration is invalid"),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp declaration_conflict(kind, details, opts) do
    name = name_to_string(Map.get(details, :name, :declaration))

    detail =
      case kind do
        :overlapping_overload ->
          " with arity #{Map.get(details, :arity)}"

        :sibling_module_collision ->
          " across modules #{inspect(Map.get(details, :owners))}"

        :overlapping_instance ->
          " for interface `#{name_to_string(Map.get(details, :interface))}` and head `#{surface_type(Map.get(details, :head))}`"

        :overlapping_named_instance ->
          " for named interface instance `#{name_to_string(Map.get(details, :name))}`"

        _ ->
          ""
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Declaration conflict",
      body: Doc.paragraph("The declaration `#{name}` conflicts with another visible declaration#{detail}."),
      primary: primary_label(opts, "rename this declaration or make its identity unique"),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp operator_conflict(kind, details, opts) do
    body =
      case kind do
        :precedence_cycle ->
          "The operator precedence declarations contain a cycle: #{inspect(details.groups)}."

        :builtin_operator_not_overloadable ->
          "The built-in operator `#{details.operator}` cannot be overloaded."
      end

    Diagnostic.new(
      code: "E106",
      key: :operator_declaration_conflict,
      severity: :error,
      title: "Operator declaration conflict",
      body: Doc.paragraph(body),
      primary: primary_label(opts, "adjust this operator declaration"),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp coverage_problem(kind, branch, context, opts) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    {title, body, label} =
      case kind do
        :missing_branch ->
          {"Incomplete pattern match", "This match does not cover the branch `#{name_to_string(branch)}`.",
           "add a branch for this constructor or a catch-all pattern"}

        :reachable_impossible ->
          {"Impossible pattern branch", "This branch can never be reached for the matched type.",
           "remove this branch or correct its pattern"}

        :duplicate_branch ->
          {"Duplicate pattern branch", "This branch repeats a constructor already handled by an earlier branch.",
           "remove the duplicate branch"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary_label(opts, label),
      payload: %{kind: kind, branch: branch, checking: Map.get(context, :checking)}
    )
  end

  defp pattern_problem(kind, details, context, opts) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))

    {title, body, label} =
      case kind do
        :forced_pattern_mismatch ->
          {"Forced pattern does not match", "This forced pattern does not match the value's expected type.",
           "change the forced pattern or its expected type"}

        :with_rematch_ctor_mismatch ->
          {"With rematch constructor mismatch",
           "The rematched value uses a different constructor than the original `with` pattern.",
           "keep the rematch constructor aligned"}

        :with_rematch_non_constructor_pattern ->
          {"With rematch must use a constructor",
           "This `with` rematch is not a constructor pattern that can be checked against the original value.",
           "rematch with the corresponding constructor"}

        :with_rematch_inconsistent_binding ->
          {"With rematch binding is inconsistent",
           "The rematch binds a name differently from the original `with` pattern.",
           "keep bindings consistent across the rematch"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary_label(opts, label),
      payload: Map.merge(%{kind: kind, checking: Map.get(context, :checking)}, details)
    )
  end

  defp known_erasure_classes_hint do
    [:pid, :reference, :integer, :float, :binary, :atom, :boolean, :list]
    |> Enum.map_join(", ", &Atom.to_string/1)
  end

  defp macro_validation_failure(kind, details, opts) do
    Diagnostic.new(
      code: "E092",
      key: :macro_validation_failed,
      severity: :error,
      title: "Macro validation failed",
      body: Doc.paragraph(macro_validation_message(kind, details)),
      primary: primary_label(opts, "this macro declaration is incomplete or inconsistent"),
      notes: ["Fix the authored macro rules or their pinned examples."],
      payload: %{kind: kind, details: details}
    )
  end

  defp macro_validation_message(:missing_diagnosis, points),
    do: "The macro does not explain every declared failure point: #{macro_failure_points(points)}."

  defp macro_validation_message(:rule_unpinned, keywords),
    do: "These macro rules have no worked example: #{inspect(keywords)}."

  defp macro_validation_message(:example_mismatch, mismatches),
    do: "These macro examples do not match their actual expansions: #{inspect(mismatches)}."

  defp macro_validation_message(:example_type_mismatch, failures),
    do: "These macro examples have the wrong type: #{inspect(failures)}."

  defp macro_validation_message(:computed_example_error, failures),
    do: "A computed macro example failed while being checked: #{inspect(failures)}."

  defp macro_failure_points(points) do
    Enum.map_join(points, ", ", fn
      {:failure, name} -> "author failure `#{name}`"
      {:hole_kind, kind} -> "#{kind} hole"
      {:keyword, keyword} -> "keyword `#{keyword}`"
      point -> inspect(point)
    end)
  end

  @spec unknown_name(atom(), term(), keyword()) :: Diagnostic.t()
  def unknown_name(namespace, name, opts \\ []) do
    spelling = name_to_string(name)
    candidate_details = rank_candidates(Keyword.get(opts, :candidates, []), spelling, namespace, opts)
    candidates = Enum.map(candidate_details, & &1.name)

    Diagnostic.new(
      code: @unknown_name_code,
      key: :unknown_name,
      severity: :error,
      title: "Unknown #{namespace_title(namespace)}",
      message: "`#{spelling}` is not available in this #{namespace} namespace.",
      primary: primary_label(opts, "`#{spelling}` was not found"),
      notes: Keyword.get(opts, :notes, []),
      suggestions: candidate_suggestions(candidate_details),
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        namespace: namespace,
        name: spelling,
        candidates: candidates,
        candidate_details: candidate_details,
        owner: Keyword.get(opts, :owner),
        checking: Keyword.get(opts, :checking),
        arity: Keyword.get(opts, :arity),
        expected_namespace: Keyword.get(opts, :expected_namespace),
        imported_from: Keyword.get(opts, :imported_from),
        kernel_context: Keyword.get(opts, :kernel_context)
      }
    )
  end

  defp primary_label(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span ->
        %Label{
          span: span,
          style: :primary,
          message: Keyword.get(opts, :label, default_message)
        }

      nil ->
        nil
    end
  end

  defp candidate_suggestions([]), do: []

  defp candidate_suggestions(candidates) do
    names = Enum.map(candidates, &suggestion_name/1)

    [
      %Suggestion{
        message: "Did you mean #{Enum.map_join(names, ", ", &"`#{&1}`")}?",
        applicability: :maybe_incorrect
      }
    ]
  end

  defp rank_candidates(candidates, spelling, namespace, opts) do
    candidates
    |> Enum.map(&candidate_detail/1)
    |> Enum.filter(&candidate_allowed?(&1, namespace, opts))
    |> Enum.sort_by(fn candidate ->
      {
        unusable_candidate?(candidate),
        candidate.namespace not in [nil, namespace],
        arity_mismatch?(candidate.arity, Keyword.get(opts, :arity)),
        candidate.visibility not in [nil, :public],
        qualification_cost(candidate),
        edit_distance(spelling, candidate.name),
        candidate.name
      }
    end)
    |> Enum.filter(&(edit_distance(spelling, &1.name) <= 2))
    |> Enum.uniq_by(& &1.name)
    |> Enum.take(3)
  end

  defp candidate_allowed?(candidate, namespace, opts) do
    candidate.namespace in [nil, namespace] and
      candidate.visibility not in [:private, "private"] and
      not arity_mismatch?(candidate.arity, Keyword.get(opts, :arity))
  end

  defp candidate_detail(candidate) when is_map(candidate) do
    %{
      name: name_to_string(Map.get(candidate, :name, Map.get(candidate, "name", "<unknown>"))),
      namespace: Map.get(candidate, :namespace, Map.get(candidate, "namespace")),
      visibility: Map.get(candidate, :visibility, Map.get(candidate, "visibility")),
      arity: Map.get(candidate, :arity, Map.get(candidate, "arity")),
      owner: Map.get(candidate, :owner, Map.get(candidate, "owner")),
      imported: Map.get(candidate, :imported, Map.get(candidate, "imported", true)),
      origin: Map.get(candidate, :origin, Map.get(candidate, "origin")),
      candidate_id: Map.get(candidate, :id, Map.get(candidate, "id", Map.get(candidate, :name)))
    }
  end

  defp candidate_detail(candidate) do
    %{
      name: name_to_string(candidate),
      namespace: nil,
      visibility: nil,
      arity: nil,
      owner: nil,
      imported: true,
      origin: nil,
      candidate_id: candidate
    }
  end

  defp suggestion_name(%{name: name, owner: owner, imported: false}) when not is_nil(owner),
    do: "#{name_to_string(owner)}.#{name}"

  defp suggestion_name(%{name: name}), do: name

  defp unusable_candidate?(%{visibility: visibility, imported: imported}),
    do: visibility == :private or imported == false

  defp arity_mismatch?(_candidate, nil), do: false
  defp arity_mismatch?(nil, _expected), do: false
  defp arity_mismatch?(candidate, expected), do: candidate != expected

  defp qualification_cost(%{owner: nil}), do: 0
  defp qualification_cost(%{imported: true}), do: 0
  defp qualification_cost(_candidate), do: 1

  defp edit_distance(left, right) do
    left = left |> String.downcase() |> String.graphemes()
    right = right |> String.downcase() |> String.graphemes()
    left_size = length(left)
    right_size = length(right)

    cond do
      left_size == 0 ->
        right_size

      right_size == 0 ->
        left_size

      true ->
        matrix =
          Enum.reduce(0..left_size, %{}, fn row, matrix ->
            Map.put(matrix, {row, 0}, row)
          end)
          |> then(fn matrix ->
            Enum.reduce(0..right_size, matrix, fn column, matrix ->
              Map.put(matrix, {0, column}, column)
            end)
          end)

        matrix =
          Enum.reduce(1..left_size, matrix, fn row, matrix ->
            Enum.reduce(1..right_size, matrix, fn column, matrix ->
              substitution =
                Map.fetch!(matrix, {row - 1, column - 1}) +
                  if(Enum.at(left, row - 1) == Enum.at(right, column - 1), do: 0, else: 1)

              transposition =
                if row > 1 and column > 1 and Enum.at(left, row - 1) == Enum.at(right, column - 2) and
                     Enum.at(left, row - 2) == Enum.at(right, column - 1) do
                  Map.fetch!(matrix, {row - 2, column - 2}) + 1
                else
                  substitution + 1
                end

              value =
                min(
                  Map.fetch!(matrix, {row - 1, column}) + 1,
                  min(Map.fetch!(matrix, {row, column - 1}) + 1, min(substitution, transposition))
                )

              Map.put(matrix, {row, column}, value)
            end)
          end)

        Map.fetch!(matrix, {left_size, right_size})
    end
  end

  defp namespace_title(:value), do: "value"
  defp namespace_title(:constructor), do: "constructor"
  defp namespace_title(:type), do: "type"
  defp namespace_title(:module), do: "module"
  defp namespace_title(:member), do: "module member"
  defp namespace_title(other), do: to_string(other)

  defp type_problem_title(%ExpectationOrigin{kind: :annotation}), do: "Annotation does not match"
  defp type_problem_title(%ExpectationOrigin{kind: :call_result}), do: "Call result has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :branch}), do: "Branches have different types"
  defp type_problem_title(%ExpectationOrigin{kind: :condition}), do: "Condition is not boolean"
  defp type_problem_title(%ExpectationOrigin{kind: :call_argument}), do: "Argument has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :application}), do: "Application has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :overload}), do: "No matching overload"
  defp type_problem_title(%ExpectationOrigin{kind: :element}), do: "Collection element has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :collection}), do: "Collection elements have different types"
  defp type_problem_title(%ExpectationOrigin{kind: :record}), do: "Record has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :record_field}), do: "Record field has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :record_update}), do: "Record update has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :pattern}), do: "Pattern has the wrong type"

  defp type_problem_title(%ExpectationOrigin{kind: :constructor_argument}),
    do: "Constructor argument has the wrong type"

  defp type_problem_title(%ExpectationOrigin{kind: :implicit}), do: "Implicit argument has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :effects}), do: "Effect is not allowed here"
  defp type_problem_title(%ExpectationOrigin{kind: :ffi}), do: "FFI boundary has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :actor}), do: "Actor message has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :fsm}), do: "FSM transition has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :supervisor}), do: "Supervisor value has the wrong type"
  defp type_problem_title(%ExpectationOrigin{kind: :operator_operand}), do: "Operator cannot use this value"
  defp type_problem_title(_origin), do: "Type mismatch"

  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_lambda}), do: "Lambda body is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :tab_not_allowed}), do: "Tabs are not valid indentation"
  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_string}), do: "String is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_char}), do: "Character is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_quoted_identifier}), do: "Quoted name is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_number}), do: "Number literal is incomplete"
  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_char_escape}), do: "Invalid character escape"
  defp syntax_problem_title(%SyntaxProblem{kind: :atom_too_long}), do: "Atom literal is too long"
  defp syntax_problem_title(%SyntaxProblem{kind: :unexpected_character}), do: "Unexpected character"
  defp syntax_problem_title(%SyntaxProblem{kind: :macro_use_mismatch}), do: "Macro syntax does not match"
  defp syntax_problem_title(%SyntaxProblem{kind: :malformed_macro_hole}), do: "Macro hole is incomplete"
  defp syntax_problem_title(%SyntaxProblem{kind: :edition_pragma_placement}), do: "Edition pragma is misplaced"
  defp syntax_problem_title(%SyntaxProblem{kind: :edition_pragma_malformed}), do: "Edition pragma is malformed"
  defp syntax_problem_title(%SyntaxProblem{kind: :edition_pragma_unknown}), do: "Edition is unknown"
  defp syntax_problem_title(%SyntaxProblem{kind: :recovered_statement}), do: "Invalid statement"
  defp syntax_problem_title(_problem), do: "I got stuck while parsing this"

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_lambda}),
    do: "This multi-statement lambda body reaches the end of its container without a closing delimiter."

  defp syntax_problem_context(%SyntaxProblem{kind: :tab_not_allowed}),
    do: "Cure indentation uses spaces so that block structure is the same in every editor."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_string}),
    do: "This string reaches the end of the source without its closing double quote."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_char}),
    do: "A character literal must contain one character and a closing single quote."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_quoted_identifier}),
    do: "This quoted name reaches the end of the source without its closing backtick."

  defp syntax_problem_context(%SyntaxProblem{kind: :invalid_number}),
    do: "This numeric prefix or exponent is missing digits required by its literal form."

  defp syntax_problem_context(%SyntaxProblem{kind: :invalid_char_escape, observed: observed}),
    do: "`\\#{syntax_name(observed)}` is not a supported character escape."

  defp syntax_problem_context(%SyntaxProblem{kind: :atom_too_long}),
    do: "BEAM atom names may contain at most 255 bytes; this authored atom exceeds that limit."

  defp syntax_problem_context(%SyntaxProblem{kind: :unexpected_character, observed: observed}),
    do: "#{syntax_name(observed)} does not begin any Cure token at this location."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :macro_use_mismatch,
         context: %{keyword: keyword},
         expected: expected,
         observed: observed
       }) do
    "The `#{keyword}` macro invocation does not match its declared syntax. " <>
      macro_expectation(expected, observed)
  end

  defp syntax_problem_context(%SyntaxProblem{kind: :malformed_macro_hole}),
    do: "This macro hole is incomplete; write it as `<name: Kind>`."

  defp syntax_problem_context(%SyntaxProblem{kind: :edition_pragma_placement}),
    do: "The edition pragma must be the first authored construct in the file."

  defp syntax_problem_context(%SyntaxProblem{kind: :edition_pragma_malformed}),
    do: "The edition pragma must contain one 4-digit year, for example `@edition(\"2026\")`."

  defp syntax_problem_context(%SyntaxProblem{kind: :edition_pragma_unknown}),
    do:
      "Unknown edition: this edition is not supported by the current compiler. " <>
        "Use one of: #{Enum.join(Cure.Edition.all(), ", ")}."

  defp syntax_problem_context(%SyntaxProblem{kind: :recovered_statement, observed: observed}),
    do:
      "The parser could not continue this statement after #{syntax_name(observed)}, so it resumed at the next statement boundary."

  defp syntax_problem_context(%SyntaxProblem{observed: :eof}),
    do: "The source ended while I was still parsing this construct."

  defp syntax_problem_context(%SyntaxProblem{observed: observed}),
    do: "#{String.capitalize(syntax_name(observed))} cannot appear at this point in the construct."

  defp syntax_expected_doc(%SyntaxProblem{expected: nil, alternatives: []}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :macro_use_mismatch}), do: Doc.empty()

  defp syntax_expected_doc(%SyntaxProblem{} = problem) do
    expected = [problem.expected | problem.alternatives] |> Enum.reject(&is_nil/1) |> Enum.map(&syntax_name/1)

    Doc.paragraph([
      "A valid continuation here starts with",
      Doc.emphasis(:expected, Enum.join(expected, " or ")) |> then(&Doc.concat([&1, Doc.text(".")]))
    ])
  end

  defp macro_expectation({:literal, expected}, observed),
    do: "expected `#{escape_macro_text(expected)}` here, but found #{macro_observed(observed)}."

  defp macro_expectation({:hole_kind, kind}, observed),
    do: "expected #{article_for_kind(kind)} #{kind} here, but found #{macro_observed(observed)}."

  defp macro_expectation(:nothing_more, observed),
    do: "This macro has no more to match here, but found #{macro_observed(observed)}."

  defp macro_expectation(expected, observed),
    do: "expected #{syntax_name(expected)} here, but found #{macro_observed(observed)}."

  defp article_for_kind(<<c, _::binary>>) when c in ~c"AEIOUaeiou", do: "an"
  defp article_for_kind(_kind), do: "a"

  defp macro_observed(:newline), do: "`end of line`"
  defp macro_observed(:dedent), do: "`a dedent`"
  defp macro_observed(nil), do: "`nil`"

  defp macro_observed({:char, value}) when is_integer(value) do
    "`'#{escape_macro_text(<<value::utf8>>)}'`"
  end

  defp macro_observed({:regex, _value}), do: "`a regex`"
  defp macro_observed(value) when is_list(value), do: "`an interpolated string`"

  defp macro_observed(value) when is_binary(value),
    do: "`#{escape_macro_text(value)}`"

  defp macro_observed(value) when is_atom(value), do: "`#{syntax_name(value)}`"
  defp macro_observed(value), do: "`#{escape_macro_text(inspect(value))}`"

  defp escape_macro_text(value) when is_binary(value) do
    value
    |> String.replace("\\", "\\\\")
    |> String.replace("\n", "\\n")
    |> String.replace("\r", "\\r")
    |> String.replace("\t", "\\t")
  end

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_lambda}), do: "the unclosed body reaches here"
  defp syntax_problem_label(%SyntaxProblem{kind: :recovered_statement}), do: "parsing resumed after this token"
  defp syntax_problem_label(_problem), do: "this syntax does not fit here"

  defp computed_macro_reason({:invalid_generated_syntax, {:raw_syntax_in_expansion, path}}),
    do:
      "invalid macro expansion: raw syntax is only valid for reflection, not generated Cure code (#{format_syntax_path(path)})"

  defp computed_macro_reason({:invalid_generated_syntax, {:quoted_syntax_in_expansion, path}}),
    do:
      "invalid macro expansion: quoted syntax must be unquoted before it is emitted as Cure code (#{format_syntax_path(path)})"

  defp computed_macro_reason({:invalid_generated_syntax, {reason, path}}),
    do: "invalid macro expansion: #{inspect(reason)} (#{format_syntax_path(path)})"

  defp computed_macro_reason({:author_diagnostics, diagnostics}) when is_list(diagnostics),
    do: "macro rejected expansion: the macro reported #{length(diagnostics)} diagnostic(s): #{inspect(diagnostics)}"

  defp computed_macro_reason({:author_failure, name, args}) when is_list(args),
    do: "macro rejected expansion: the macro reported `#{name}`: #{inspect(args)}"

  defp computed_macro_reason(reason), do: inspect(reason)

  defp format_syntax_path(path) do
    path
    |> Enum.reverse()
    |> Enum.map_join(".", fn
      {:child, index} -> "child[#{index}]"
      {:attribute, key, index} -> "attribute #{key}[#{index}]"
      {:syntax_literal} -> "syntax literal"
      {:map_key} -> "map key"
      {:map_value} -> "map value"
      {:list_item} -> "list item"
      other -> inspect(other)
    end)
  end

  defp syntax_secondary_labels(%SyntaxProblem{opener: %Span{} = opener}, primary_span) when opener != primary_span,
    do: [%Label{span: opener, style: :secondary, message: "the construct starts here"}]

  defp syntax_secondary_labels(%SyntaxProblem{within: %Span{} = within}, primary_span) when within != primary_span,
    do: [%Label{span: within, style: :secondary, message: "while parsing this construct"}]

  defp syntax_secondary_labels(_problem, _primary_span), do: []

  defp syntax_insertions(%SyntaxProblem{observed: :eof, expected: expected}, %Span{} = span) do
    case syntax_insertion(expected) do
      nil ->
        []

      replacement ->
        [
          %Suggestion{
            message: "Insert `#{replacement}` to close the construct",
            applicability: :machine_applicable,
            edits: [
              %TextEdit{
                span: %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column},
                replacement: replacement
              }
            ]
          }
        ]
    end
  end

  defp syntax_insertions(_problem, _span), do: []

  defp syntax_insertion(:rparen), do: ")"
  defp syntax_insertion(:rbracket), do: "]"
  defp syntax_insertion(:rbrace), do: "}"
  defp syntax_insertion(:end), do: "end"
  defp syntax_insertion(:double_quote), do: "\""
  defp syntax_insertion(:single_quote), do: "'"
  defp syntax_insertion(:backtick), do: "`"
  defp syntax_insertion(_expected), do: nil

  defp lex_problem({:tab_not_allowed, line, column}, opts),
    do: syntax_problem(:tab_not_allowed, nil, :tab, line, column, opts)

  defp lex_problem({:unterminated_string, line, column}, opts),
    do: syntax_problem(:unterminated_string, :double_quote, :eof, line, column, opts)

  defp lex_problem({:unterminated_char, line, column}, opts),
    do: syntax_problem(:unterminated_char, :single_quote, :eof, line, column, opts)

  defp lex_problem({:unterminated_quoted_identifier, line, column}, opts),
    do: syntax_problem(:unterminated_quoted_identifier, :backtick, :eof, line, column, opts)

  defp lex_problem({kind, line, column}, opts)
       when kind in [:invalid_hex_literal, :invalid_binary_literal, :invalid_float_literal],
       do: syntax_problem(:invalid_number, :digits, kind, line, column, opts)

  defp lex_problem({:invalid_char_escape, line, column}, opts),
    do: syntax_problem(:invalid_char_escape, :valid_escape, :escape, line, column, opts)

  defp lex_problem({:atom_too_long, line, column}, opts),
    do: syntax_problem(:atom_too_long, :shorter_atom, :atom, line, column, opts)

  defp lex_problem({:unexpected_character, character, line, column}, opts),
    do: syntax_problem(:unexpected_character, :token, character, line, column, opts)

  defp lex_problem(reason, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: {:lex_error, reason})

  defp syntax_problem(kind, expected, observed, line, column, opts) do
    %SyntaxProblem{
      kind: kind,
      expected: expected,
      observed: observed,
      at: Keyword.get(opts, :span),
      context: %{line: line, column: column}
    }
  end

  defp type_problem_context(%ExpectationOrigin{kind: :annotation}),
    do: "This expression does not match the type written in its annotation."

  defp type_problem_context(%ExpectationOrigin{kind: :call_result, owner: owner}),
    do: "The result of `#{name_to_string(owner || "this call")}` does not match the surrounding expectation."

  defp type_problem_context(%ExpectationOrigin{kind: :branch}),
    do: "Every branch of this expression must produce the same type."

  defp type_problem_context(%ExpectationOrigin{kind: :condition}),
    do: "A condition must produce `Bool` before either branch can run."

  defp type_problem_context(%ExpectationOrigin{kind: :call_argument, index: index, owner: owner}),
    do: "Argument #{display_index(index)} of `#{name_to_string(owner || "this function")}` has an incompatible type."

  defp type_problem_context(%ExpectationOrigin{kind: :operator_operand, owner: owner}),
    do: "The `#{name_to_string(owner || "operator")}` operator cannot use this operand type."

  defp type_problem_context(%ExpectationOrigin{kind: :element, index: index}),
    do: "Element #{display_index(index)} of this collection has an incompatible type."

  defp type_problem_context(%ExpectationOrigin{kind: :collection}),
    do: "All elements of this collection must agree on one type."

  defp type_problem_context(%ExpectationOrigin{kind: :record, owner: owner}),
    do: "This value does not match the declared shape of record `#{name_to_string(owner || "this record")}`."

  defp type_problem_context(%ExpectationOrigin{kind: :record_field, owner: owner}),
    do: "Field `#{name_to_string(owner || "this field")}` does not match the record's declared field type."

  defp type_problem_context(%ExpectationOrigin{kind: :record_update, owner: owner}),
    do: "This record update does not preserve the declared record shape of `#{name_to_string(owner || "this record")}`."

  defp type_problem_context(%ExpectationOrigin{kind: :pattern}),
    do: "This pattern must match the type of the value it is checking."

  defp type_problem_context(%ExpectationOrigin{kind: :constructor_argument, index: index, owner: owner}),
    do:
      "Argument #{display_index(index)} of constructor `#{name_to_string(owner || "this constructor")}` has an incompatible type."

  defp type_problem_context(%ExpectationOrigin{kind: :implicit, owner: owner}),
    do: "The implicit argument required by `#{name_to_string(owner || "this call")}` has the wrong type."

  defp type_problem_context(%ExpectationOrigin{kind: :effects}),
    do: "This expression performs an effect that is not allowed in its context."

  defp type_problem_context(%ExpectationOrigin{kind: :ffi, owner: owner}),
    do: "The FFI boundary `#{name_to_string(owner || "this declaration")}` does not match its Cure type."

  defp type_problem_context(%ExpectationOrigin{kind: :actor, owner: owner}),
    do: "Actor `#{name_to_string(owner || "this actor")}` received a value with the wrong message type."

  defp type_problem_context(%ExpectationOrigin{kind: :fsm, owner: owner}),
    do: "FSM transition `#{name_to_string(owner || "this transition")}` does not produce the required state type."

  defp type_problem_context(%ExpectationOrigin{kind: :supervisor, owner: owner}),
    do:
      "Supervisor `#{name_to_string(owner || "this supervisor")}` does not match the required child specification type."

  defp type_problem_context(_origin), do: "This expression has a different type than its context requires."

  # The labels take the same width, keeping the first type character in both
  # rows aligned for quick visual comparison. Core terms retain enough shape to
  # colour only the divergent descendants; strings and unrelated roots stay
  # uncoloured because a textual resemblance is not semantic evidence.
  defp type_comparison_doc(expected, actual) do
    {expected_doc, actual_doc} = type_difference_docs(printable_core(expected), printable_core(actual), false)

    Doc.concat([
      Doc.concat(["Expected: ", expected_doc]),
      Doc.text("\n"),
      Doc.concat(["Found:    ", actual_doc])
    ])
  end

  defp type_difference_docs(expected, actual, _within_common?) when expected == actual do
    {plain_type_doc(expected), plain_type_doc(actual)}
  end

  defp type_difference_docs(
         {:data, name, expected_params, expected_indices},
         {:data, name, actual_params, actual_indices},
         _within_common?
       )
       when length(expected_params) == length(actual_params) and length(expected_indices) == length(actual_indices) do
    type_application_docs(
      Cure.Elab.Name.base(name),
      expected_params ++ expected_indices,
      actual_params ++ actual_indices
    )
  end

  defp type_difference_docs({:ctor, name, expected_args}, {:ctor, name, actual_args}, _within_common?)
       when length(expected_args) == length(actual_args) do
    type_application_docs(Cure.Elab.Name.base(name), expected_args, actual_args)
  end

  defp type_difference_docs({:app, expected_fun, expected_arg}, {:app, actual_fun, actual_arg}, _within_common?) do
    {expected_fun_doc, actual_fun_doc} = type_difference_docs(expected_fun, actual_fun, true)
    {expected_arg_doc, actual_arg_doc} = type_difference_docs(expected_arg, actual_arg, true)

    {
      Doc.concat([expected_fun_doc, Doc.text(" "), expected_arg_doc]),
      Doc.concat([actual_fun_doc, Doc.text(" "), actual_arg_doc])
    }
  end

  defp type_difference_docs(expected, actual, true) do
    {
      Doc.emphasis(:expected, plain_type_doc(expected)),
      Doc.emphasis(:observed, plain_type_doc(actual))
    }
  end

  defp type_difference_docs(expected, actual, false) do
    {plain_type_doc(expected), plain_type_doc(actual)}
  end

  defp type_application_docs(head, expected_args, actual_args) do
    {expected_args, actual_args} =
      expected_args
      |> Enum.zip(actual_args)
      |> Enum.map(&type_difference_docs(elem(&1, 0), elem(&1, 1), true))
      |> Enum.unzip()

    {
      type_application_doc(head, expected_args),
      type_application_doc(head, actual_args)
    }
  end

  defp type_application_doc(head, []), do: Doc.text(head)

  defp type_application_doc(head, args) do
    args_doc = args |> Enum.intersperse(Doc.text(", ")) |> Doc.concat()
    Doc.concat([Doc.text(head), Doc.text("("), args_doc, Doc.text(")")])
  end

  # Some diagnostic entry points already provide a user-facing type string.
  # Do not pass those through Core's printer, which would render them as quoted
  # Elixir strings rather than as the type the user wrote.
  defp plain_type_doc(type) when is_binary(type), do: Doc.text(type)
  defp plain_type_doc(type), do: Doc.text(print_core(type))

  defp type_problem_label(%ExpectationOrigin{kind: :condition}), do: "this condition has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :call_result}), do: "this call result has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :branch}), do: "this branch disagrees with another branch"
  defp type_problem_label(%ExpectationOrigin{kind: :call_argument}), do: "this argument has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :application}), do: "this application has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :element}), do: "this collection element has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :collection}), do: "this collection element has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :record}), do: "this record has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :record_field}), do: "this record field has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :record_update}), do: "this record update has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :pattern}), do: "this pattern has the wrong type"

  defp type_problem_label(%ExpectationOrigin{kind: :constructor_argument}),
    do: "this constructor argument has the wrong type"

  defp type_problem_label(%ExpectationOrigin{kind: :implicit}), do: "this implicit argument has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :effects}), do: "this expression has an invalid effect"
  defp type_problem_label(%ExpectationOrigin{kind: :ffi}), do: "this FFI boundary has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :actor}), do: "this actor message has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :fsm}), do: "this FSM transition has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :supervisor}), do: "this supervisor value has the wrong type"
  defp type_problem_label(_origin), do: "this expression has the wrong type"

  defp expectation_labels(%ExpectationOrigin{span: %Span{} = span}, primary_span, _related)
       when span != primary_span,
       do: [%Label{span: span, style: :secondary, message: "the expectation comes from here"}]

  defp expectation_labels(_origin, primary_span, %Span{} = related) when related != primary_span,
    do: [%Label{span: related, style: :secondary, message: "the compared expression is here"}]

  defp expectation_labels(_origin, _primary_span, _related), do: []

  defp display_index(nil), do: ""
  defp display_index(index), do: index + 1

  defp surface_type(type) when is_binary(type), do: type
  defp surface_type(type), do: print_core(type)

  defp macro_title(macro), do: macro |> name_to_string() |> String.capitalize()

  defp macro_failure_message(macro, module, %Diagnostic{} = cause) do
    "The `#{macro}` declaration could not generate `#{module}`. #{Diagnostic.message(cause)}"
  end

  defp provenance_frames(details, opts) do
    source = Map.get(details, :source_provenance) || %{}
    chain = Map.get(details, :expansion_provenance, [])
    invocation = Keyword.get(opts, :span)

    frames =
      Enum.map(chain, fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword) || "macro",
          invocation: invocation
        }
      end)

    source_frame =
      case Map.get(source, :macro) do
        nil -> []
        macro -> [%ProvenanceFrame{kind: :macro_expansion, name: macro, invocation: invocation}]
      end

    (frames ++ source_frame)
    |> Enum.uniq_by(& &1.name)
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)

  defp print_core(term) do
    term
    |> printable_core()
    |> Cure.Core.Printer.print()
  rescue
    ArgumentError -> inspect(term)
  end

  defp printable_core(term) when is_tuple(term) do
    case term |> elem(0) |> Atom.to_string() do
      "v" <> _ -> Cure.Core.Quote.reify(term, 0)
      _ -> term
    end
  end

  defp printable_core(term), do: term

  # Parser errors retain token *kinds* for stable machine handling. Translate
  # punctuation and operators back to the spelling a user sees in the source;
  # `:arrow` and `:rparen` are implementation names, whereas `->` and `)` tell
  # the user precisely what needs attention.
  @syntax_token_spellings %{
    lparen: "(",
    rparen: ")",
    lbracket: "[",
    rbracket: "]",
    lbrace: "{",
    rbrace: "}",
    splice_open: "$(",
    tuple_open: "%[",
    map_open: "%{",
    binary_open: "<<",
    binary_close: ">>",
    comma: ",",
    semicolon: ";",
    colon: ":",
    colon_colon: "::",
    dot: ".",
    ellipsis: "...",
    range: "..",
    range_inclusive: "..=",
    arrow: "->",
    fat_arrow: "=>",
    assign: "=",
    plus_assign: "+=",
    minus_assign: "-=",
    star_assign: "*=",
    slash_assign: "/=",
    plus: "+",
    minus: "-",
    star: "*",
    slash: "/",
    eq: "==",
    neq: "!=",
    lt: "<",
    lte: "<=",
    gt: ">",
    gte: ">=",
    pipe: "|>",
    bar: "|",
    at: "@",
    caret: "^",
    percent: "%",
    bang: "!",
    string_concat: "<>",
    melquiades: "✉",
    double_quote: "\"",
    single_quote: "'",
    backtick: "`"
  }

  defp syntax_name(name) when is_map_key(@syntax_token_spellings, name),
    do: "'#{Map.fetch!(@syntax_token_spellings, name)}'"

  defp syntax_name(:eof), do: "the end of the file"
  defp syntax_name(:newline), do: "a new line"
  defp syntax_name(:indent), do: "an indented block"
  defp syntax_name(:dedent), do: "the end of this block"
  defp syntax_name(:identifier), do: "an identifier"
  defp syntax_name(:keyword), do: "a keyword"
  defp syntax_name(:integer), do: "an integer"
  defp syntax_name(:float), do: "a number"
  defp syntax_name(:string), do: "a string"
  defp syntax_name(:char), do: "a character"
  defp syntax_name(:atom), do: "an atom"
  defp syntax_name(:bool), do: "a boolean"
  defp syntax_name(:hole), do: "a hole"
  defp syntax_name(:macro_hole), do: "a macro hole"
  defp syntax_name({:literal, value}), do: "the literal #{inspect(value)}"
  defp syntax_name(name) when is_binary(name), do: "'#{name}'"
  defp syntax_name(name) when is_atom(name), do: "'#{name}'"
  defp syntax_name(name), do: inspect(name)
end
