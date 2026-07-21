defmodule Cure.Diagnostic.Adapter do
  @moduledoc "Converts phase-specific and legacy error values into shared diagnostics."

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    DefiningEquationProblem,
    ExpectationOrigin,
    Label,
    ProvenanceFrame,
    ProofChainMismatchProblem,
    ProofChainSyntaxProblem,
    RewriteProblem,
    Span,
    Suggestion,
    SyntaxProblem,
    TextEdit,
    TypeProblem
  }

  alias Cure.Diagnostic.Operational
  alias Cure.Diagnostic.Suggest

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
             :duplicate_index,
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

  def from_error({:proof_chain_syntax, %ProofChainSyntaxProblem{} = problem}, opts) do
    {title, message, label} =
      case problem.kind do
        :empty_chain ->
          {"Proof chain is empty", "A proof chain needs a first expression and at least one justified equality step.",
           "add the first expression and an equality step"}

        :missing_relation ->
          {"Proof chain step is missing `==`",
           "Every chain step must relate the previous endpoint to a new endpoint with `==`.",
           "add `==` and the next endpoint"}

        :missing_right_side ->
          {"Proof chain step has no endpoint",
           "The `==` relation must be followed by the expression reached by this step.",
           "add the right-hand expression"}

        :missing_because ->
          {"Proof chain step needs a reason",
           "Every equality step must include `because` followed by checked evidence.", "add `because` and its evidence"}

        :first_step_previous ->
          {"Proof chain cannot start with `_`", "There is no previous endpoint at the beginning of a proof chain.",
           "write the first expression explicitly"}

        :unreachable_proof_statement ->
          {"Proof statement is unreachable",
           "An earlier expression already closed this justification, so this later statement cannot contribute evidence.",
           "this statement is unreachable"}

        _ ->
          {"Malformed proof chain", "This proof chain does not have the required equational structure.",
           "repair this proof-chain step"}
      end

    suggestions =
      if problem.kind == :missing_because and match?(%Span{}, problem.insertion) do
        [
          %Suggestion{
            message: "Insert `because`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: problem.insertion, replacement: "because "}]
          }
        ]
      else
        []
      end

    Diagnostic.new(
      code: "E109",
      key: :proof_chain_syntax,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      secondary: proof_chain_syntax_labels(problem, Keyword.get(opts, :span)),
      suggestions: suggestions,
      payload: problem
    )
  end

  def from_error({:proof_chain_mismatch, %ProofChainMismatchProblem{} = problem}, opts) do
    displayed = problem.step_index + 1

    {title, message, label} =
      case problem.kind do
        :unfinished_justification ->
          {"Proof justification is unfinished",
           "The justification for step #{displayed} ended while its equality goal was still open. Add a final evidence expression; the structured payload lists the residual goal and available local facts.",
           "this block ends without proving its goal"}

        :adjacent_endpoints ->
          {"Proof chain endpoints have different types",
           "The endpoint written for step #{displayed} does not have the same carrier type as the previous endpoint.",
           "this endpoint has the wrong type"}

        _ ->
          {"Proof does not justify chain step #{displayed}",
           "The evidence after `because` does not prove the equality required by step #{displayed}. Each step is checked independently before the chain is composed.",
           "this evidence proves a different proposition"}
      end

    Diagnostic.new(
      code: "E110",
      key: :proof_chain_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      secondary: proof_chain_mismatch_labels(problem, Keyword.get(opts, :span)),
      payload: problem
    )
  end

  def from_error({:rewrite_failed, %RewriteProblem{} = problem}, opts) do
    {title, message, label} =
      case problem.kind do
        :no_occurrence ->
          {"Rewrite has no matching occurrence",
           "The selected side of this equality does not occur in the current proof goal.",
           "nothing in this goal matches the rewrite"}

        :ambiguous_occurrence ->
          {"Rewrite matches more than once",
           "This equality matches multiple places. Select one of the numbered occurrences with `at n`.",
           "choose which occurrence to rewrite"}

        :invalid_occurrence ->
          {"Rewrite occurrence does not exist",
           "The requested occurrence number is outside the candidates in the current goal.",
           "this occurrence number is not available"}

        :bad_target ->
          {"Rewrite target is not a local hypothesis",
           "The name after `in` must identify a local proof hypothesis in this justification.",
           "this rewrite target is unavailable"}

        :reverse_only ->
          {"Rewrite only matches in the opposite direction",
           "The other side of this equality occurs in the goal. Add or remove `backwards` to use that direction.",
           "this direction has no match"}

        _ ->
          {"Rewrite theorem is not an equality",
           "The expression after `using` must prove Cure's `Equivalent` proposition.",
           "this expression is not equality evidence"}
      end

    Diagnostic.new(
      code: "E111",
      key: :rewrite_failed,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      secondary: rewrite_labels(problem, Keyword.get(opts, :span)),
      suggestions: rewrite_suggestions(problem),
      payload: problem
    )
  end

  def from_error({:defining_equation_unavailable, %DefiningEquationProblem{} = problem}, opts) do
    {title, message, label} =
      case problem.kind do
        :inaccessible_equation ->
          {"Defining equation is private", "This generated equation follows its function's private visibility.",
           "this equation is not visible here"}

        :friendly_name_collision ->
          {"Defining equation name is ambiguous",
           "More than one certified branch has this friendly constructor name. Select its structural pattern key.",
           "this friendly equation name is ambiguous"}

        _ ->
          {"Defining equation is unavailable",
           "This function has no certified defining equation with the requested constructor path.",
           "no such defining equation is available"}
      end

    Diagnostic.new(
      code: "E114",
      key: :defining_equation_unavailable,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      secondary: defining_equation_labels(problem, Keyword.get(opts, :span)),
      payload: problem
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

  def from_error({:source_context, :branch_type, context}, opts) when is_map(context) do
    branch_type_failure(context, opts)
  end

  def from_error({:source_context, {:branch_type, details}, context}, opts) when is_map(context) do
    branch_type_failure(Map.put(context, :branch_details, details), opts)
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

  def from_error({:unknown_field, record, field, available_fields}, opts) when is_list(available_fields) do
    candidates =
      Enum.map(available_fields, fn candidate ->
        %{
          id: {:record_field, record, candidate},
          name: name_to_string(candidate),
          namespace: :member,
          owner: record,
          imported: true,
          origin: :record_shape
        }
      end)

    opts =
      opts
      |> Keyword.put(:owner, record)
      |> Keyword.put(:record, record)
      |> Keyword.put(:candidates, candidates)
      |> Keyword.put(:display_name, "#{name_to_string(record)}.#{name_to_string(field)}")

    unknown_name(:member, name_to_string(field), opts)
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

  def from_error({:no_such_interface, interface}, opts),
    do: unknown_name(:interface, interface, opts)

  def from_error({:unknown_interface_method, interface, method}, opts),
    do: unknown_name(:member, method, Keyword.put(opts, :checking, interface))

  def from_error({:missing_method, interface, method}, opts),
    do: interface_failure(:missing_method, %{interface: interface, method: method}, opts)

  def from_error({:method_signature_mismatch, interface, method}, opts),
    do: interface_failure(:method_signature_mismatch, %{interface: interface, method: method}, opts)

  def from_error({:instance_head_ill_formed, reason}, opts),
    do: interface_failure(:instance_head_ill_formed, %{reason: reason}, opts)

  def from_error({:missing_superinterface, interface, super_interface, head}, opts),
    do:
      interface_failure(
        :missing_superinterface,
        %{interface: interface, superinterface: super_interface, head: head},
        opts
      )

  def from_error({:union_member_not_ground, member}, opts),
    do: union_declaration_failure(:union_member_not_ground, %{member: member}, opts)

  def from_error({:unsupported_member_shape, members}, opts),
    do: union_declaration_failure(:unsupported_member_shape, %{members: members}, opts)

  def from_error({:same_runtime_shape, members}, opts),
    do: union_declaration_failure(:same_runtime_shape, %{members: members}, opts)

  def from_error({:same_erased_literal, members}, opts),
    do: union_declaration_failure(:same_erased_literal, %{members: members}, opts)

  def from_error({:cannot_derive, interface}, opts),
    do: deriving_failure(:cannot_derive, %{interface: interface}, opts)

  def from_error({:deriving_needs_strings, interface}, opts),
    do: deriving_failure(:deriving_needs_strings, %{interface: interface}, opts)

  def from_error({:deriving_needs_constraints, interface, type_name}, opts),
    do: deriving_failure(:deriving_needs_constraints, %{interface: interface, type: type_name}, opts)

  def from_error({:cannot_derive_shape, interface, type_name}, opts),
    do: deriving_failure(:cannot_derive_shape, %{interface: interface, type: type_name}, opts)

  def from_error({:cannot_derive_method, interface, method, reason}, opts),
    do: deriving_failure(:cannot_derive_method, %{interface: interface, method: method, reason: reason}, opts)

  def from_error({:missing_stdlib_source, source, path}, _opts),
    do: Cure.Diagnostic.Operational.file_read(path || source, :enoent)

  def from_error({:missing_stdlib_source_dir, source}, _opts),
    do: Cure.Diagnostic.Operational.file_read(source, :enoent)

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
      {{:index_mismatch, {:cannot_unify, actual, expected}}, origin} when not is_nil(origin) ->
        contextual_type_problem(:index_mismatch, actual, expected, origin, context, opts)

      {{:cannot_unify, actual, expected}, origin} when not is_nil(origin) ->
        contextual_type_problem(:cannot_unify, actual, expected, origin, context, opts)

      {{:conversion_failure, actual, expected}, origin} when not is_nil(origin) ->
        from_error(
          %TypeProblem{
            kind: :conversion_failure,
            actual: actual,
            expected: expected,
            origin: %ExpectationOrigin{
              kind: origin,
              span: Keyword.get(opts, :span, Map.get(context, :expectation_span)),
              owner: Map.get(context, :checking),
              index: Map.get(context, :argument_index)
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

  def from_error({:index_mismatch, _details}, opts),
    do: kernel_type_failure(:index_mismatch, opts)

  def from_error({:cannot_unify, _actual, _expected}, opts),
    do: kernel_type_failure(:cannot_unify, opts)

  def from_error({:escaping_variable, _id}, opts),
    do: kernel_type_failure(:escaping_variable, opts)

  def from_error({:hole_in_inference_position, name}, opts),
    do: kernel_type_failure(:hole_in_inference_position, Keyword.put(opts, :name, name))

  def from_error({:ctor_requires_checking_mode, family}, opts),
    do: kernel_type_failure(:ctor_requires_checking_mode, Keyword.put(opts, :family, family))

  def from_error({:bounded_bound_not_concrete, bound}, opts),
    do: kernel_type_failure(:bounded_bound_not_concrete, Keyword.put(opts, :bound, bound))

  def from_error({:cyclic_typealiases, aliases}, opts),
    do: declaration_conflict(:cyclic_typealiases, %{aliases: aliases}, opts)

  def from_error({:module_identity_missing, path}, _opts),
    do: Cure.Diagnostic.Operational.file_read(path, :module_identity_missing)

  def from_error({:module_identity_mismatch, requested, declared, path}, opts),
    do: declaration_conflict(:module_identity_mismatch, %{requested: requested, declared: declared, path: path}, opts)

  def from_error({:module_path_identity_mismatch, path, declared, requested}, opts),
    do:
      declaration_conflict(
        :module_path_identity_mismatch,
        %{path: path, declared: declared, requested: requested},
        opts
      )

  def from_error({:char_literal_needs_bounded, value}, opts),
    do: contextual_type_failure(:char_literal_needs_bounded, %{value: value}, opts)

  def from_error({:char_literal_out_of_range, value}, opts),
    do: contextual_type_failure(:char_literal_out_of_range, %{value: value}, opts)

  def from_error({:extern_returns_union, name, codomain}, opts),
    do: contextual_type_failure(:extern_returns_union, %{name: name, codomain: codomain}, opts)

  def from_error({:extern_union_indistinct, name, reason}, opts),
    do: contextual_type_failure(:extern_union_indistinct, %{name: name, reason: reason}, opts)

  def from_error({:cannot_infer_dependent_match, branch}, opts),
    do: contextual_type_failure(:cannot_infer_dependent_match, %{branch: branch}, opts)

  def from_error({:bidirectional_erased_field, constructor}, opts),
    do: contextual_type_failure(:bidirectional_erased_field, %{constructor: constructor}, opts)

  def from_error({:generated_hole_not_well_typed, term}, opts),
    do: macro_validation_failure(:generated_hole_not_well_typed, %{term: term}, opts)

  def from_error({:example_use_site_not_fully_consumed, _unused, _ast}, opts),
    do: macro_validation_failure(:example_use_site_not_fully_consumed, %{}, opts)

  def from_error({:closed_category_extension, categories}, opts),
    do: macro_validation_failure(:closed_category_extension, %{categories: categories}, opts)

  def from_error({:duplicate_unit, suffix}, opts),
    do: macro_validation_failure(:duplicate_unit, %{suffix: suffix}, opts)

  # These are public macro-library validation boundaries. Keep them in the
  # macro family so users are directed to the authored board/unit declaration,
  # rather than seeing an internal tuple or a generic compiler failure.
  def from_error({kind, detail}, opts)
      when kind in [:invalid_unit, :unknown_unit, :invalid_board_name],
      do: macro_validation_failure(kind, %{detail: detail}, opts)

  # Some trusted checking paths can return the bare verdict after their
  # declaration wrapper has been stripped. Keep that verdict contextual rather
  # than falling through to the unhelpful generic "Elaboration failed" title.
  def from_error(:branch_type, opts), do: branch_type_failure(%{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_board_pins,
             :invalid_board_capabilities,
             :invalid_board_buses,
             :invalid_board_flash,
             :flash_offset_out_of_bounds
           ],
      do: macro_validation_failure(kind, %{}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_packet_name,
             :invalid_packet_endian,
             :unknown_packet_scalar,
             :missing_packet_endian,
             :forward_packet_length,
             :invalid_packet_crc_fields,
             :invalid_packet_field,
             :invalid_packet_field_name,
             :duplicate_packet_field,
             :invalid_macro_rules,
             :accepts_without_syntax_family,
             :accepts_without_expander,
             :expander_without_accepts,
             :multiple_accepts_declarations,
             :multiple_expands_declarations,
             :invalid_driver_base,
             :invalid_driver_register,
             :duplicate_driver_register,
             :overlapping_driver_register,
             :module_rule_not_fully_consumed,
             :not_a_module_rule,
             :ambiguous_macro_extension,
             :invalid_macro_diagnostics,
             :invalid_macro_diagnostic,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair,
             :left_recursive_parse_production,
             :protocol_role_count,
             :invalid_macro_segment,
             :unsupported_surface_filler,
             :missing_hole_filler,
             :unsupported_hole_type,
             :invalid_lift_module,
             :invalid_lift_module_name,
             :invalid_lift_callback,
             :invalid_module_name,
             :invalid_behaviour,
             :invalid_lift_declaration,
             :invalid_lift_import,
             :invalid_lift_module_ast,
             :lifted_module_dependency_cycle,
             :duplicate_lifted_module,
             :invalid_generated_syntax,
             :unknown_syntax_family,
             :duplicate_syntax_family,
             :duplicate_syntax_family_field,
             :syntax_family_cycle,
             :primitive_missing_builtin,
             :unknown_primitive_tag,
             :primitive_floor_mismatch,
             :unsupported_declaration,
             :invalid_syntax_node,
             :invalid_syntax_leaf,
             :invalid_syntax_failure,
             :unsupported_syntax_core,
             :raw_syntax_in_expansion,
             :quoted_syntax_in_expansion,
             :malformed_expansion_syntax,
             :malformed_expansion_attribute,
             :malformed_expansion_map,
             :malformed_expansion_literal,
             :malformed_reflected_syntax,
             :malformed_reflected_attribute,
             :malformed_reflected_literal,
             :malformed_reflected_map,
             :invalid_syntax_attrs,
             :unknown_reducer_constructor,
             :incomplete_reducer,
             :unsupported_hole_arity
           ],
      do: macro_validation_failure(kind, %{detail: detail}, opts)

  def from_error({kind, first, second}, opts)
      when kind in [:forward_packet_length, :invalid_packet_crc_fields, :reserved_syntax_field, :invalid_unit_literal],
      do: macro_validation_failure(kind, %{first: first, second: second}, opts)

  # C2/Core artifact decoding is an untrusted boundary. Its failures are
  # operational artifact diagnostics, not kernel terms to expose in default
  # output. The detail is retained only as machine/debug data by the
  # operational converter.
  def from_error({:bad_grade, grade}, _opts),
    do:
      Operational.artifact_error("Core artifact contains an invalid relevance grade", %{kind: :bad_grade, grade: grade})

  def from_error({:unknown_symbol, symbol}, _opts),
    do: Operational.artifact_error("Core artifact contains an unknown symbol", %{kind: :unknown_symbol, symbol: symbol})

  def from_error({:ill_formed_term, term}, _opts),
    do: Operational.artifact_error("Core artifact contains an ill-formed term", %{kind: :ill_formed_term, term: term})

  def from_error({:reducer_arity, constructor, actual, expected}, opts),
    do:
      macro_validation_failure(
        :reducer_arity,
        %{constructor: constructor, actual: actual, expected: expected},
        opts
      )

  def from_error({:primitive_floor_mismatch, name, node, other}, opts),
    do: macro_validation_failure(:primitive_floor_mismatch, %{name: name, node: node, other: other}, opts)

  def from_error(kind, opts)
      when kind in [
             :bounded_family_unregistered,
             :absurd_in_reachable_position,
             :opaque_not_eliminable,
             :case_scrutinee_not_data,
             :not_total,
             :not_a_function,
             :coverage,
             :branch_arity,
             :index_arity
           ],
      do: contextual_type_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :no_compatible_macro_input,
             :normalization_fuel_exhausted,
             :invalid_parse_production,
             :duplicate_parse_production,
             :invalid_macro_diagnostics,
             :invalid_macro_diagnostic,
             :invalid_syntax_attr,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair,
             :invalid_check_property,
             :duplicate_check_property,
             :invalid_protocol_role,
             :duplicate_protocol_role,
             :duplicate_reducer_constructor,
             :not_a_nat,
             :invalid_lift_module_ast,
             :invalid_lift_callback,
             :invalid_lift_declaration,
             :invalid_lift_import,
             :invalid_driver_register,
             :duplicate_driver_register,
             :overlapping_driver_register,
             :module_rule_not_fully_consumed,
             :not_a_module_rule,
             :expander_without_accepts,
             :accepts_without_syntax_family,
             :accepts_without_expander,
             :multiple_accepts_declarations,
             :multiple_expands_declarations
           ],
      do: macro_validation_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :applied_non_function,
             :rewrite_requires_expected_type,
             :rewrite_proof_not_equality,
             :match_scrutinee_not_data,
             :with_mixed_rematch_arms,
             :with_scrutinee_not_data,
             :too_few_arguments,
             :too_many_arguments,
             :nonvariable_scrutinee
           ],
      do: contextual_type_failure(kind, %{}, opts)

  def from_error(:shadowed, opts),
    do: declaration_conflict(:shadowed, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :arg_arity,
             :ctor_arity,
             :domain_mismatch,
             :grade_mismatch,
             :bad_motive,
             :not_a_type,
             :not_a_type_value,
             :index_mismatch,
             :universe_level,
             :universe_ceiling,
             :hole_in_inference_position,
             :ctor_requires_checking_mode,
             :bounded_bound_not_concrete
           ] do
    kernel_type_failure(kind, opts)
  end

  def from_error({:occurs_check, id, _term}, opts),
    do: kernel_type_failure(:occurs_check, Keyword.put(opts, :variable, id))

  def from_error({:no_instance, interface, head}, opts),
    do: contextual_type_failure(:no_instance, %{interface: interface, head: head}, opts)

  def from_error({:ambiguous_instance_for_expected_type, interface, expected}, opts),
    do: contextual_type_failure(:ambiguous_instance, %{interface: interface, expected: expected}, opts)

  def from_error({:no_matching_overload, name, arguments}, opts),
    do: contextual_type_failure(:no_matching_overload, %{name: name, arguments: arguments}, opts)

  def from_error({:label_mismatch, key, declared, written}, opts),
    do:
      contextual_type_failure(
        :label_mismatch,
        %{key: key, declared: declared, written: written},
        opts
      )

  def from_error({:ambiguous_overload, name, owners}, opts),
    do: contextual_type_failure(:ambiguous_overload, %{name: name, owners: owners}, opts)

  def from_error({:ambiguous_method, method, interfaces}, opts),
    do: ambiguous_member(method, interfaces, opts)

  def from_error({:projection_not_a_record, record}, opts),
    do: contextual_type_failure(:projection_not_a_record, %{record: record}, opts)

  def from_error({:bad_projection, details}, opts),
    do: contextual_type_failure(:bad_projection, %{details: details}, opts)

  def from_error({:typed_pattern_arity, position}, opts),
    do: arity_failure(:typed_pattern, %{position: position}, opts)

  def from_error({:typed_pattern_type_error, reason}, opts),
    do: contextual_type_failure(:typed_pattern_type_error, %{reason: reason}, opts)

  def from_error({:unsolved_index, constructor}, opts),
    do: contextual_type_failure(:unsolved_index, %{constructor: constructor}, opts)

  def from_error({:unsolved_field_type, constructor}, opts),
    do: contextual_type_failure(:unsolved_field_type, %{constructor: constructor}, opts)

  def from_error({:forced_pattern_not_in_pattern, meta}, opts),
    do: contextual_type_failure(:forced_pattern_not_in_pattern, %{detail: meta}, opts)

  def from_error({:named_implicit_not_in_pattern, meta}, opts),
    do: contextual_type_failure(:named_implicit_not_in_pattern, %{detail: meta}, opts)

  def from_error({:unsolved_parameters, constructor}, opts),
    do: contextual_type_failure(:unsolved_parameters, %{constructor: constructor}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :unsupported_expression,
             :unsupported_pattern,
             :unsupported_guard,
             :untyped_parameter,
             :let_needs_annotation,
             :graded_let_needs_annotation,
             :binary_match_needs_default,
             :map_match_needs_default,
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :typealias_not_a_type,
             :result_type_not_family,
             :constructor_result_mismatch,
             :dependent_record_projection,
             :with_indexed_scrutinee_unsupported,
             :with_rematch_unsupported_parent_pattern,
             :with_sibling_dependency_unsupported,
             :telescope_index_out_of_bounds,
             :effect_binder_erased
           ],
      do: contextual_type_failure(kind, %{detail: detail}, opts)

  def from_error({:effect_arity, name, expected, actual}, opts),
    do: contextual_type_failure(:effect_arity, %{name: name, expected: expected, actual: actual}, opts)

  def from_error({:unknown_global, name}, opts),
    do: unknown_name(:value, name, opts)

  def from_error({:unbound_var, name}, opts),
    do: unknown_name(:value, name, opts)

  def from_error({:unknown_family, name}, opts),
    do: unknown_name(:type, name, opts)

  def from_error({:unknown_ctor, name}, opts),
    do: unknown_name(:constructor, name, opts)

  def from_error({:foreign_ctor, name}, opts),
    do: unknown_name(:constructor, name, opts)

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

  def from_error({:expected, expected, :got, actual, line, column, %Span{} = span}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :unexpected_token,
        expected: expected,
        observed: actual,
        at: Keyword.get(opts, :span, span),
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

  def from_error({:expected_token, expected, actual_type, actual_value, line, column, %Span{} = span}, opts) do
    from_error(
      %SyntaxProblem{
        kind: :unexpected_token,
        expected: expected,
        observed: if(is_nil(actual_value), do: actual_type, else: actual_value),
        at: Keyword.get(opts, :span, span),
        context: %{line: line, column: column, token_type: actual_type}
      },
      opts
    )
  end

  def from_error({:expected_literal_capture, shape, line, column}, opts),
    do:
      from_error(
        %SyntaxProblem{
          kind: :macro_literal_capture,
          expected: shape,
          observed: :non_literal,
          at: Keyword.get(opts, :span),
          context: %{line: line, column: column, code: "E094"}
        },
        opts
      )

  def from_error({:unknown_syntax_family_field, family, field, line, column}, opts),
    do:
      macro_validation_failure(
        :unknown_syntax_family_field,
        %{family: family, field: field, line: line, column: column},
        opts
      )

  def from_error({:missing_syntax_family_field, family, field, line, column}, opts),
    do:
      macro_validation_failure(
        :missing_syntax_family_field,
        %{family: family, field: field, line: line, column: column},
        opts
      )

  def from_error({:unknown_macro_obligation_capture, capture, line, column}, opts),
    do:
      macro_validation_failure(:unknown_macro_obligation_capture, %{capture: capture, line: line, column: column}, opts)

  def from_error({:graded_let_requires_variable, grade, line, column}, opts),
    do: contextual_type_failure(:graded_let_requires_variable, %{grade: grade, line: line, column: column}, opts)

  def from_error({:unknown_grade, grade, line, column}, opts),
    do: contextual_type_failure(:unknown_grade, %{grade: grade, line: line, column: column}, opts)

  def from_error({:grade_requires_type, name, grade, line, column}, opts),
    do: contextual_type_failure(:grade_requires_type, %{name: name, grade: grade, line: line, column: column}, opts)

  def from_error({:unit_type_reserved, name}, opts),
    do: macro_validation_failure(:unit_type_reserved, %{name: name}, opts)

  def from_error({:unit_type_reserved, name, line, column}, opts),
    do: macro_validation_failure(:unit_type_reserved, %{name: name, line: line, column: column}, opts)

  def from_error({:duplicate_syntax_family_field, field, line, column}, opts),
    do: macro_validation_failure(:duplicate_syntax_family_field, %{field: field, line: line, column: column}, opts)

  def from_error({:non_associative, operator, :chained_with, next_operator, line, column}, opts),
    do:
      from_error(
        %SyntaxProblem{
          kind: :non_associative,
          expected: :parentheses,
          observed: next_operator,
          at: Keyword.get(opts, :span),
          context: %{line: line, column: column, operator: operator}
        },
        opts
      )

  def from_error({:ambiguous_precedence, left_group, right_group, line, column}, opts),
    do:
      from_error(
        %SyntaxProblem{
          kind: :ambiguous_precedence,
          expected: :parentheses,
          observed: right_group,
          at: Keyword.get(opts, :span),
          context: %{line: line, column: column, left_group: left_group}
        },
        opts
      )

  def from_error({:with_multi_proof_unsupported, message}, opts),
    do: contextual_type_failure(:with_multi_proof_unsupported, %{message: message}, opts)

  def from_error({:with_multi_rematch_unsupported, message}, opts),
    do: contextual_type_failure(:with_multi_rematch_unsupported, %{message: message}, opts)

  def from_error({:with_multi_arity_mismatch, message}, opts),
    do: contextual_type_failure(:with_multi_arity_mismatch, %{message: message}, opts)

  def from_error({:with_multi_proof_unsupported, message, meta}, opts),
    do: contextual_type_failure(:with_multi_proof_unsupported, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_rematch_unsupported, message, meta}, opts),
    do: contextual_type_failure(:with_multi_rematch_unsupported, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_arity_mismatch, message, meta}, opts),
    do: contextual_type_failure(:with_multi_arity_mismatch, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_no_arms, message, meta}, opts),
    do: contextual_type_failure(:with_multi_no_arms, %{message: message, meta: meta}, opts)

  def from_error({:with_multi_inconsistent_pattern, message, meta}, opts),
    do: contextual_type_failure(:with_multi_inconsistent_pattern, %{message: message, meta: meta}, opts)

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

  def from_error({:invalid_macro_family, reason, line, column}, opts)
      when is_integer(line) and is_integer(column) do
    diagnostic = macro_validation_failure(:invalid_macro_family, reason, opts)
    %{diagnostic | payload: Map.merge(diagnostic.payload, %{line: line, column: column})}
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
  def from_error({:cannot_emit, reason}, opts), do: codegen_failure({:cannot_emit, reason}, opts)

  def from_error({:inconsistent_head_kind, name}, opts),
    do: declaration_conflict(:inconsistent_head_kind, %{name: name}, opts)

  def from_error({:lift_module_error, details}, opts) when is_map(details) do
    macro = get_in(details, [:source_provenance, :macro]) || :macro
    cause = Map.get(details, :cause)

    case family_type_failure(cause, details, opts) do
      {:ok, diagnostic} ->
        diagnostic

      :error ->
        cause_diagnostic = from_error(cause)

        Diagnostic.new(
          code: "E092",
          key: :macro_expansion_failed,
          severity: :error,
          title: "#{macro_title(macro)} expansion failed",
          message: macro_failure_message(macro, details.module, cause_diagnostic),
          primary: primary_label(opts, "this `#{macro}` declaration generated the failing module"),
          notes: ["The generated module is an implementation detail; edit the authored `#{macro}` declaration instead."],
          provenance: provenance_frames(details, opts),
          payload: %{
            macro: name_to_string(macro),
            module: name_to_string(details.module),
            behaviour: Map.get(details, :behaviour),
            cause: %{code: cause_diagnostic.code, key: cause_diagnostic.key, payload: cause_diagnostic.payload}
          }
        )
    end
  end

  def from_error({kind, detail}, opts)
      when kind in [
             :bad_result_type,
             :non_integer_index,
             :unsupported_index_literal,
             :unsupported_index_expr,
             :unsupported_index_operator,
             :sigma_projection_needs_ctx,
             :unsupported_comprehension_pattern,
             :unsupported_binary_generator_pattern,
             :unsupported_binary_segment,
             :unsupported_binary_match_arm,
             :unsupported_map_match_arm,
             :unsupported_map_value_pattern,
             :unsupported_map_key_pattern,
             :unsupported_block_statement,
             :unsupported_block,
             :unknown_macro_failure,
             :unsolved_metavariable_in_type,
             :lambda_expected_pi,
             :missing_raw_delimiter
           ],
      do: contextual_type_failure(kind, %{detail: detail}, opts)

  def from_error({kind, first, second}, opts)
      when kind in [:rewrite_no_match, :non_uniform_parameter, :bounded_lit_out_of_range],
      do: contextual_type_failure(kind, %{first: first, second: second}, opts)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  # Generated OTP callbacks still represent authored family sections. Preserve
  # a real type relation at that boundary instead of presenting it as E092.
  defp family_type_failure({:source_context, reason, context}, details, opts)
       when is_map(context) do
    with origin when not is_nil(origin) <- family_origin(details) do
      context =
        context
        |> Map.put(:expectation_origin, origin)
        |> Map.put(:checking, Map.get(details, :module))

      if reason_kind?(reason) do
        {:ok, from_error({:source_context, reason, context}, opts)}
      else
        if family_boundary_reason?(reason) do
          {:ok, family_boundary_failure(origin, details, reason, opts)}
        else
          :error
        end
      end
    else
      _ -> :error
    end
  end

  defp family_type_failure(_cause, _details, _opts), do: :error

  defp reason_kind?({:cannot_unify, _, _}), do: true
  defp reason_kind?({:index_mismatch, {:cannot_unify, _, _}}), do: true
  defp reason_kind?({:conversion_failure, _, _}), do: true
  defp reason_kind?(_reason), do: false

  defp family_boundary_reason?({:foreign_ctor, _}), do: true
  defp family_boundary_reason?({:unknown_ctor, _}), do: true
  defp family_boundary_reason?(_reason), do: false

  defp family_boundary_failure(origin, details, reason, opts) do
    family = family_origin_name(origin)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "#{family} callback has the wrong type",
      body:
        Doc.paragraph(
          "This authored #{String.downcase(family)} callback does not produce the protocol value required by its generated module."
        ),
      primary: primary_label(opts, "this #{String.downcase(family)} callback has the wrong type"),
      provenance: provenance_frames(details, opts),
      payload: %{
        origin: %{kind: origin, owner: Map.get(details, :module)},
        cause: inspect(reason),
        module: Map.get(details, :module),
        behaviour: Map.get(details, :behaviour)
      }
    )
  end

  defp family_origin_name(:actor), do: "Actor"
  defp family_origin_name(:fsm), do: "FSM"
  defp family_origin_name(:supervisor), do: "Supervisor"

  defp family_origin(details) do
    case Map.get(details, :behaviour) do
      :gen_server -> :actor
      :gen_statem -> :fsm
      :supervisor -> :supervisor
      _ -> nil
    end
  end

  defp contextual_type_problem(kind, actual, expected, origin, context, opts) do
    from_error(
      %TypeProblem{
        kind: kind,
        actual: actual,
        expected: expected,
        origin: %ExpectationOrigin{
          kind: origin,
          span: Keyword.get(opts, :span, Map.get(context, :expectation_span)),
          owner: Map.get(context, :checking),
          index: Map.get(context, :argument_index)
        },
        expression: Map.get(context, :expression_category, :expression),
        span: Keyword.get(opts, :span, Map.get(context, :span)),
        debug: %{cause: {kind, actual, expected}, checking: Map.get(context, :checking)}
      },
      opts
    )
  end

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
          "`@erases(#{name_to_string(details.class)})` on `#{name_to_string(details.name)}` is not a supported erasure class. Supported classes: #{known_erasure_classes_hint()}."

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
          " across modules #{Enum.map_join(Map.get(details, :owners, []), ", ", &name_to_string/1)}"

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

  defp interface_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :missing_method ->
          {"Interface method is missing",
           "The implementation of `#{name_to_string(details.interface)}` does not define required method `#{name_to_string(details.method)}`.",
           "implement this required method"}

        :method_signature_mismatch ->
          {"Interface method signature mismatch",
           "Method `#{name_to_string(details.method)}` does not match the signature required by `#{name_to_string(details.interface)}`.",
           "make this method match the interface signature"}

        :instance_head_ill_formed ->
          {"Instance head is not well formed",
           "The interface instance head cannot be used as a valid implementation head.",
           "use a well-formed instance head"}

        :missing_superinterface ->
          {"Required superinterface is missing",
           "Interface `#{name_to_string(details.interface)}` requires `#{name_to_string(details.superinterface)}` for this implementation.",
           "implement the required superinterface first"}
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp union_declaration_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :union_member_not_ground ->
          {"Union member is not ground", "Every union member must be a concrete, fully-resolved type.",
           "make this union member concrete"}

        :unsupported_member_shape ->
          {"Unsupported union member shape", "This union member has a runtime shape that Cure cannot represent safely.",
           "use a supported union member shape"}

        :same_runtime_shape ->
          {"Union members have the same runtime shape",
           "Two union members erase to the same runtime representation and cannot be distinguished.",
           "change one member's runtime shape"}

        :same_erased_literal ->
          {"Union members have the same erased literal",
           "Two union members erase to the same literal value and would overlap at runtime.",
           "use distinct literal values"}
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp deriving_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :cannot_derive ->
          {"Cannot derive interface",
           "Cure cannot derive interface `#{name_to_string(details.interface)}` for this declaration.",
           "provide the required deriving implementation"}

        :deriving_needs_strings ->
          {"Deriving requires string support",
           "Interface `#{name_to_string(details.interface)}` can only be derived for a type with string-compatible members.",
           "use string-compatible members or implement the interface manually"}

        :deriving_needs_constraints ->
          {"Deriving constraints are not satisfied",
           "Deriving `#{name_to_string(details.interface)}` for `#{name_to_string(details.type)}` requires constraints that are not available.",
           "add the required constraints or implement the interface manually"}

        :cannot_derive_shape ->
          {"Cannot derive for this type shape",
           "Interface `#{name_to_string(details.interface)}` cannot be derived for `#{name_to_string(details.type)}` because its shape is unsupported.",
           "change the type shape or implement the interface manually"}

        :cannot_derive_method ->
          {"Cannot derive interface method",
           "Method `#{name_to_string(details.method)}` of `#{name_to_string(details.interface)}` cannot be generated for this type.",
           "implement this method explicitly"}
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp operator_conflict(kind, details, opts) do
    body =
      case kind do
        :precedence_cycle ->
          "The operator precedence declarations contain a cycle among #{Enum.map_join(details.groups, ", ", &name_to_string/1)}."

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

  defp kernel_type_failure(kind, opts) do
    {title, message, label} =
      case kind do
        :index_mismatch ->
          {"Dependent index mismatch", "A dependent index does not agree with the value required by this expression.",
           "make the indexed values agree"}

        :cannot_unify ->
          {"Types cannot be unified", "The type checker could not make these types definitionally equal.",
           "change the expression or annotation so the types agree"}

        :escaping_variable ->
          {"Type variable escapes its scope", "A type variable would escape the scope in which it was introduced.",
           "keep this type variable within its binding"}

        :occurs_check ->
          {"Infinite type detected", "A type variable would have to contain itself, producing an infinite type.",
           "break the recursive type equation"}

        :arg_arity ->
          {"Wrong number of type arguments",
           "This type application has a different number of arguments than its declaration.",
           "supply exactly the declared arguments"}

        :ctor_arity ->
          {"Wrong number of constructor arguments",
           "This constructor application has a different number of arguments than its declaration.",
           "supply exactly the constructor arguments"}

        :domain_mismatch ->
          {"Function domain mismatch", "This function is being applied to a value of the wrong type.",
           "change the argument to match the function domain"}

        :grade_mismatch ->
          {"Relevance grade mismatch", "This value is used with a relevance grade that its type does not allow.",
           "use the value at its declared relevance"}

        :bad_motive ->
          {"Invalid case motive", "The dependent case motive is not a well-formed type family.",
           "make the case motive a function over the scrutinee"}

        :not_a_type ->
          {"Expected a type", "This expression does not evaluate to a type where one is required.",
           "use a type expression here"}

        :not_a_type_value ->
          {"Expected a type value", "This expression is not a valid type value in this position.",
           "use a well-formed type value"}

        :universe_level ->
          {"Universe level mismatch", "This type lives above the universe level allowed here.",
           "lower the universe level or widen the surrounding type"}

        :universe_ceiling ->
          {"Universe level is too high", "This type would exceed Cure's supported universe ceiling.",
           "reduce the universe level"}

        :hole_in_inference_position ->
          {"Hole needs an expected type", "This hole appears where the kernel cannot infer its type.",
           "add an annotation that determines the hole's type"}

        :ctor_requires_checking_mode ->
          {"Constructor needs an expected type", "This constructor cannot be inferred without checking information.",
           "add a type annotation at the constructor use"}

        :bounded_bound_not_concrete ->
          {"Bound must be concrete", "This bounded type declaration requires a concrete bound.",
           "replace the bound with a concrete value"}

        :bounded_family_unregistered ->
          {"Bounded literal type is unavailable", "This literal requires the standard Bounded type family.",
           "import or register the Bounded type family"}

        :absurd_in_reachable_position ->
          {"Impossible branch is reachable", "This absurd branch is reachable in the current type.",
           "make the branch unreachable or prove the contradiction"}

        :opaque_not_eliminable ->
          {"Opaque value cannot be eliminated", "This opaque value cannot be reduced or matched here.",
           "use the public interface of the opaque value"}

        :case_scrutinee_not_data ->
          {"Case scrutinee is not data", "A case expression must scrutinize a data value.",
           "match on a data constructor"}

        :not_total ->
          {"Definition is not total", "This definition is used in a total context but is not total.",
           "cover every case or remove the total-context use"}

        :not_a_function ->
          {"Application target is not a function", "This expression is applied but has no function type.",
           "apply a function-valued expression"}

        :coverage ->
          {"Pattern match is not exhaustive", "This pattern match does not cover every possible value.",
           "add the missing pattern or a default arm"}

        :branch_arity ->
          {"Pattern branch has the wrong arity", "The branch binds a different number of fields than its constructor.",
           "make the pattern match the constructor fields"}

        :branch_type ->
          {"Pattern branches disagree", "The branches of this expression do not produce one compatible type.",
           "make every branch return the same type"}

        :index_arity ->
          {"Indexed type has the wrong number of indices", "This indexed application does not match its declaration.",
           "supply exactly the declared indices"}

        _ ->
          {"Kernel type check failed", "The kernel could not validate this type or term.",
           "add an annotation or revise the term"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      payload: %{kind: kind}
    )
  end

  defp branch_type_failure(context, opts) do
    opts = Keyword.put_new(opts, :span, Map.get(context, :span))
    branches = Keyword.get(opts, :branch_patterns, Map.get(context, :branch_patterns, []))
    branch_names = Enum.map(branches, &branch_name/1)
    checking = Map.get(context, :checking)
    subject = if checking, do: " in `#{checking}`", else: ""
    details = Map.get(context, :branch_details, %{})
    branch_details = Map.get(details, :branches, [])

    selected_detail =
      case Enum.find(branch_details, &match?({:error, _}, Map.get(&1, :status))) do
        nil -> List.first(branch_details, details)
        detail -> detail
      end

    failing = Map.get(selected_detail, :constructor)
    actual = Map.get(selected_detail, :actual)
    expected = Map.get(selected_detail, :expected)
    singleton_branches = singleton_type_branches(branch_details)

    detail =
      case {singleton_branches, failing, actual, expected} do
        {[{constructor, type}], _, _, _} ->
          "Possible outlier: only the `#{name_to_string(constructor)}` branch has type `#{type}`; check it against the other branches and the declared result."

        {_, constructor, actual, expected}
        when not is_nil(constructor) and not is_nil(actual) and not is_nil(expected) ->
          "Possible outlier: the `#{name_to_string(constructor)}` branch has type `#{surface_type(actual)}`, but the declared result requires `#{surface_type(expected)}`."

        _ ->
          case branch_names do
            [first, second | rest] ->
              names = Enum.map_join([first, second | rest], ", ", &"`#{&1}`")

              "The branches #{names} of this match are checked against the declared result, but at least one branch does not produce that result."

            _ ->
              "Every branch of this match is checked against the declared result type."
          end
      end

    labels =
      Enum.map(branches, fn branch ->
        span = branch_span(branch)
        name = branch_name(branch)

        message =
          if same_branch?(name, failing),
            do: "possible outlier: this branch has the incompatible type",
            else: "compare this branch with the declared result"

        %Label{span: span, style: :primary, message: message}
      end)
      |> Enum.reject(&is_nil(&1.span))

    {primary, secondary} =
      case labels do
        [first | rest] -> {first, rest}
        [] -> {primary_label(opts, "make these branches return the same type"), []}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Pattern branches disagree#{subject}",
      body:
        Doc.stack([
          Doc.paragraph(detail),
          Doc.paragraph("Check each branch expression against the result type written after the function name.")
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

  defp branch_name(%{name: name}), do: to_string(name)
  defp branch_name(name), do: to_string(name)

  defp same_branch?(_name, nil), do: false

  defp same_branch?(name, failing) do
    name = to_string(name)
    failing = to_string(failing)
    failing == name or String.ends_with?(failing, "#" <> name) or String.ends_with?(failing, "." <> name)
  end

  defp singleton_type_branches(details) do
    groups =
      details
      |> Enum.filter(&(not is_nil(Map.get(&1, :actual))))
      |> Enum.group_by(&surface_type(&1.actual))

    if map_size(groups) > 1 and Enum.any?(groups, fn {_type, entries} -> length(entries) > 1 end) do
      groups
      |> Enum.filter(fn {_type, entries} -> length(entries) == 1 end)
      |> Enum.map(fn {type, [entry]} -> {entry.constructor, type} end)
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

  defp branch_span(%{span: %Cure.Diagnostic.Span{} = span}), do: span
  defp branch_span(_branch), do: nil

  defp contextual_type_failure(kind, details, opts) do
    {title, message, label} =
      case kind do
        :no_instance ->
          {"No instance found",
           "Cure could not find an implementation of `#{name_to_string(details.interface)}` for the required type `#{surface_type(details.head)}`.",
           "add or import an instance for this type"}

        :ambiguous_instance ->
          {"Instance resolution is ambiguous",
           "More than one `#{name_to_string(details.interface)}` instance can satisfy this expected type.",
           "make the instance selection unambiguous"}

        :no_matching_overload ->
          {"No matching overload",
           "No overload of `#{name_to_string(details.name)}` accepts the argument types at this call site.",
           "change the arguments or choose a different overload"}

        :label_mismatch ->
          {"Argument label mismatch",
           "The argument label `#{name_to_string(details.key)}` does not match the labels declared by this overload.",
           "use the declared argument label"}

        :ambiguous_overload ->
          {"Overload resolution is ambiguous",
           "More than one overload of `#{name_to_string(details.name)}` matches this call.",
           "add an annotation or qualify the overload"}

        :projection_not_a_record ->
          {"Record projection requires a record", "This projection was applied to a value that is not a record.",
           "project a field from a record value"}

        :bad_projection ->
          {"Invalid record projection", "This record projection is not valid for the value's type.",
           "use a field declared by the record"}

        :typed_pattern_type_error ->
          {"Pattern annotation does not match",
           "The type annotation on this pattern is incompatible with the value it matches.",
           "change the pattern or its annotation"}

        :unsolved_index ->
          {"Indexed constructor has an unresolved index",
           "Cure could not determine an index required by this constructor.",
           "provide an annotation or make the index explicit"}

        :unsolved_field_type ->
          {"Constructor field type is unresolved", "Cure could not determine the type of a field in this constructor.",
           "add an annotation that determines the field type"}

        :forced_pattern_not_in_pattern ->
          {"Forced pattern is unavailable", "This forced pattern refers to a name that is not bound by the pattern.",
           "bind the name in the pattern before forcing it"}

        :named_implicit_not_in_pattern ->
          {"Named implicit is unavailable", "This named implicit is not bound by the surrounding pattern.",
           "bind the implicit in the pattern or remove the reference"}

        :unsolved_parameters ->
          {"Constructor parameters are unresolved",
           "Cure could not determine all parameters required by this constructor.",
           "add an annotation or make the constructor parameters explicit"}

        :unsupported_expression ->
          {"Expression is not supported here", "This expression form is not valid in the current elaboration context.",
           "rewrite this expression using a supported form"}

        :unsupported_pattern ->
          {"Pattern is not supported here", "This pattern form cannot be checked in the current context.",
           "use a supported pattern"}

        :unsupported_guard ->
          {"Guard is not supported here", "This guard expression cannot be used in a pattern guard.",
           "rewrite the guard using supported operations"}

        :untyped_parameter ->
          {"Parameter needs a type", "This parameter must have an explicit type annotation here.",
           "add a type annotation to the parameter"}

        :let_needs_annotation ->
          {"Binding needs an annotation", "Cure cannot infer the type of this binding from its initializer.",
           "add a type annotation to this binding"}

        :graded_let_needs_annotation ->
          {"Graded binding needs an annotation",
           "A graded binding must state the type required by its relevance grade.",
           "add a type annotation to this graded binding"}

        :binary_match_needs_default ->
          {"Binary match needs a default", "This binary match does not cover all possible segment lengths.",
           "add a default binary-match arm"}

        :map_match_needs_default ->
          {"Map match needs a default", "This map match does not cover unmatched keys.", "add a default map-match arm"}

        :nonlinear_pattern ->
          {"Pattern binds a name twice", "A pattern cannot bind the same name more than once.",
           "use distinct names or a forced pattern"}

        :duplicate_default_pattern ->
          {"Duplicate default pattern", "This match contains more than one default pattern.",
           "keep only one default pattern"}

        :impossible_default_pattern ->
          {"Default pattern is unreachable", "This default pattern cannot be reached after the earlier patterns.",
           "remove or revise the unreachable pattern"}

        :typealias_not_a_type ->
          {"Type alias does not name a type", "The right-hand side of this type alias is not a well-formed type.",
           "define the alias using a type expression"}

        :result_type_not_family ->
          {"Result type is not a type family",
           "This dependent result must be a type family indexed by the function's result.",
           "return a valid indexed type"}

        :constructor_result_mismatch ->
          {"Constructor result does not match",
           "This constructor's result type does not match the family being defined.",
           "correct the constructor result indices"}

        :dependent_record_projection ->
          {"Dependent record projection is invalid",
           "This record field projection does not preserve the required dependent type.",
           "project a field with a compatible dependent type"}

        :with_indexed_scrutinee_unsupported ->
          {"Indexed with-scrutinee is unsupported",
           "This indexed value cannot be used as the parent of a `with` rematch.", "rematch a supported parent value"}

        :with_rematch_unsupported_parent_pattern ->
          {"With parent pattern is unsupported",
           "The parent pattern cannot be structurally rematched in this `with` expression.",
           "use a supported parent pattern"}

        :with_sibling_dependency_unsupported ->
          {"With sibling dependency is unsupported",
           "This rematch depends on a sibling binding that is not available here.",
           "restructure the dependent bindings"}

        :telescope_index_out_of_bounds ->
          {"Dependent index is out of scope", "This indexed reference points outside the available telescope.",
           "use an index that is in scope"}

        :effect_binder_erased ->
          {"Effect binder is erased", "An erased effect binder is used where a runtime-relevant value is required.",
           "make the binder relevant or remove the runtime use"}

        :effect_arity ->
          {"Effect operation arity mismatch", "This effect operation was given the wrong number of arguments.",
           "provide the arguments required by the effect operation"}

        :char_literal_needs_bounded ->
          {"Character literal needs a bound", "This character literal requires an explicit bounded character type.",
           "add the required bounded character annotation"}

        :char_literal_out_of_range ->
          {"Character literal is out of range", "This character value is outside the supported character range.",
           "use a valid character literal"}

        :extern_returns_union ->
          {"Extern return type is unsupported", "An extern declaration cannot return this union type.",
           "use a representable foreign return type"}

        :extern_union_indistinct ->
          {"Extern union is indistinct", "The extern union members cannot be distinguished at the foreign boundary.",
           "make the foreign union members representationally distinct"}

        :cannot_infer_dependent_match ->
          {"Dependent match needs an expected type", "Cure cannot infer the indexed result of this match expression.",
           "add an annotation that determines the dependent result"}

        :bidirectional_erased_field ->
          {"Erased field cannot be inferred here", "This erased constructor field requires checking information.",
           "add an annotation or make the field relevant"}

        :applied_non_function ->
          {"Application target is not callable", "This expression is applied but does not have a callable type.",
           "apply a function or constructor"}

        :rewrite_requires_expected_type ->
          {"Rewrite needs an expected type", "Cure cannot infer the type required by this rewrite.",
           "add an annotation that fixes the rewritten type"}

        :rewrite_proof_not_equality ->
          {"Rewrite proof is not an equality", "The proof supplied to rewrite does not prove an equality.",
           "use an equality proof for the value being rewritten"}

        :match_scrutinee_not_data ->
          {"Match scrutinee is not data", "This match expression scrutinizes a value without data constructors.",
           "match a data value"}

        :with_mixed_rematch_arms ->
          {"With arms use incompatible rematches", "The rematch arms of this with expression do not have one shape.",
           "use the same rematch form in every arm"}

        :with_scrutinee_not_data ->
          {"With scrutinee is not data", "A with rematch requires a data-valued scrutinee.", "rematch a data value"}

        :too_few_arguments ->
          {"Too few arguments", "This application does not provide every required argument.",
           "supply the remaining arguments"}

        :too_many_arguments ->
          {"Too many arguments", "This application provides more arguments than the declaration accepts.",
           "remove the extra arguments"}

        :nonvariable_scrutinee ->
          {"Scrutinee must be a variable", "This dependent operation requires a variable scrutinee.",
           "bind the scrutinee before using it"}

        :graded_let_requires_variable ->
          {"Graded binding needs a variable", "A graded binding must bind a variable so its relevance can be tracked.",
           "bind a variable before applying the grade"}

        :unknown_grade ->
          {"Unknown relevance grade", "The written relevance grade is not defined by the current language edition.",
           "use a supported relevance grade"}

        :grade_requires_type ->
          {"Graded binding needs a type", "A graded binding must declare the type whose usage is being restricted.",
           "add a type annotation to the graded binding"}

        :with_multi_proof_unsupported ->
          {"Multiple with-scrutinee proof is unsupported",
           "A `proof` binding cannot be combined with multiple `with` scrutinees in this form.",
           "use one scrutinee or move the proof binding into a separate match"}

        :with_multi_rematch_unsupported ->
          {"Multiple with-scrutinee rematch is unsupported",
           "An LHS rematch cannot be combined with multiple `with` scrutinees in this form.",
           "use one scrutinee or restructure the rematch"}

        :with_multi_arity_mismatch ->
          {"Multiple with-arm arity mismatch",
           "Each arm of a multiple-scrutinee `with` must provide one pattern per scrutinee.",
           "make the arm pattern count match the scrutinee count"}

        :with_multi_no_arms ->
          {"Multiple with-scrutinee has no arms", "A multiple-scrutinee `with` must contain at least one matching arm.",
           "add a `with` arm"}

        :with_multi_inconsistent_pattern ->
          {"Multiple with patterns disagree",
           "Multiple-scrutinee `with` arms must use structurally consistent outer patterns.",
           "make the outer patterns agree or split the match"}

        :branch_arity ->
          {"Pattern branch has the wrong arity",
           "A pattern branch does not bind the number of values required by the matched constructor.",
           "make the branch pattern match the constructor's arguments"}

        :coverage ->
          {"Pattern match is not exhaustive", "This pattern match does not cover every constructor that can reach it.",
           "add the missing branch or a final wildcard branch"}

        :index_arity ->
          {"Indexed type has the wrong arity",
           "The number of indices supplied to this indexed type does not match its declaration.",
           "supply exactly the declared indices"}

        _ ->
          {"Elaboration failed", "This expression or declaration is not valid in the current checking context.",
           "change the source construct or add an annotation"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp ambiguous_member(method, interfaces, opts) do
    spelling = name_to_string(method)
    owners = Enum.map(interfaces, &name_to_string/1)

    Diagnostic.new(
      code: "E089",
      key: :ambiguous_name,
      severity: :error,
      title: "Ambiguous interface method",
      body: Doc.paragraph("Method `#{spelling}` is declared by more than one visible interface."),
      primary: primary_label(opts, "qualify or disambiguate this method"),
      suggestions: [
        %Suggestion{
          message: "Choose one of #{Enum.map_join(owners, ", ", &"`#{&1}`")}",
          applicability: :manual
        }
      ],
      payload: %{kind: :ambiguous_method, method: spelling, interfaces: owners}
    )
  end

  defp arity_failure(kind, details, opts) do
    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Pattern arity mismatch",
      body: Doc.paragraph("This typed pattern has the wrong number of elements at position #{details.position}."),
      primary: primary_label(opts, "make the pattern arity match the value"),
      payload: Map.put(details, :kind, kind)
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
    do: "These macro rules have no worked example: #{Enum.join(Enum.map(keywords, &name_to_string/1), ", ")}."

  defp macro_validation_message(:example_mismatch, mismatches),
    do: "Macro example(s) do not match their actual expansions: #{macro_example_names(mismatches)}."

  defp macro_validation_message(:example_type_mismatch, failures),
    do: "Macro example(s) have the wrong type: #{macro_example_names(failures)}."

  defp macro_validation_message(:computed_example_error, failures),
    do: "A computed macro example failed while being checked: #{macro_example_names(failures)}."

  defp macro_validation_message(:invalid_macro_family, _reason),
    do: "The macro's syntax-family declarations are inconsistent."

  defp macro_validation_message(:generated_hole_not_well_typed, _details),
    do: "A generated hole is not well typed."

  defp macro_validation_message(:example_use_site_not_fully_consumed, _details),
    do: "A macro example did not consume the complete use site."

  defp macro_validation_message(:closed_category_extension, _details),
    do: "A closed macro category was extended unexpectedly."

  defp macro_validation_message(:duplicate_unit, _details),
    do: "A macro literal unit was declared more than once."

  defp macro_validation_message(kind, _details),
    do: "Macro validation failed for #{name_to_string(kind)}."

  defp macro_failure_points(points) do
    Enum.map_join(points, ", ", fn
      {:failure, name} -> "author failure `#{name}`"
      {:hole_kind, kind} -> "#{kind} hole"
      {:keyword, keyword} -> "keyword `#{keyword}`"
      _point -> "an additional declared failure point"
    end)
  end

  defp macro_example_names(values) when is_list(values) do
    names =
      values
      |> Enum.map(fn
        %{keyword: keyword} -> name_to_string(keyword)
        %{"keyword" => keyword} -> name_to_string(keyword)
        _ -> nil
      end)
      |> Enum.reject(&is_nil/1)

    case names do
      [] -> "the affected examples"
      names -> Enum.join(names, ", ")
    end
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
      message: "`#{Keyword.get(opts, :display_name, spelling)}` is not available in this #{namespace} namespace.",
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
        record: Keyword.get(opts, :record),
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

  defp proof_chain_syntax_labels(problem, primary) do
    construct_message =
      if problem.kind == :unreachable_proof_statement,
        do: "the goal was already closed here",
        else: "this proof chain starts here"

    [
      {problem.construct, construct_message},
      {problem.step,
       if(problem.kind == :unreachable_proof_statement,
         do: "this statement is unreachable",
         else: "this step is incomplete"
       )}
    ]
    |> Enum.flat_map(fn
      {%Span{} = span, message} when span != primary -> [%Label{span: span, style: :secondary, message: message}]
      _ -> []
    end)
  end

  defp proof_chain_mismatch_labels(problem, primary) do
    [
      {problem.current_step, "step #{problem.step_index + 1} requires this equality"},
      {problem.previous_step, "the previous endpoint is established here"}
    ]
    |> Enum.flat_map(fn
      {%Span{} = span, message} when span != primary -> [%Label{span: span, style: :secondary, message: message}]
      _ -> []
    end)
  end

  defp rewrite_labels(problem, primary) do
    [
      {problem.command, "rewrite command"},
      {problem.theorem, "equality supplied here"},
      {problem.goal, "current proof goal"}
    ]
    |> Enum.flat_map(fn
      {%Span{} = span, message} when span != primary -> [%Label{span: span, style: :secondary, message: message}]
      _ -> []
    end)
  end

  defp rewrite_suggestions(%RewriteProblem{kind: :ambiguous_occurrence, command: %Span{} = command} = problem) do
    insertion = %Span{
      command
      | start_byte: command.end_byte,
        start_line: command.end_line,
        start_column: command.end_column
    }

    Enum.map(problem.occurrences || [], fn occurrence ->
      %Suggestion{
        message: "Rewrite occurrence #{occurrence.number}",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: insertion, replacement: " at #{occurrence.number}"}]
      }
    end)
  end

  defp rewrite_suggestions(%RewriteProblem{kind: :reverse_only, command: %Span{} = command, direction: direction}) do
    {span, replacement} =
      case direction do
        :forward ->
          {%Span{
             command
             | start_byte: command.start_byte + 7,
               end_byte: command.start_byte + 7,
               start_column: command.start_column + 7,
               end_line: command.start_line,
               end_column: command.start_column + 7
           }, " backwards"}

        :backwards ->
          {%Span{
             command
             | start_byte: command.start_byte + 7,
               end_byte: command.start_byte + 17,
               start_column: command.start_column + 7,
               end_line: command.start_line,
               end_column: command.start_column + 17
           }, ""}
      end

    [
      %Suggestion{
        message: "Use the opposite rewrite direction",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: replacement}]
      }
    ]
  end

  defp rewrite_suggestions(_problem), do: []

  defp defining_equation_labels(problem, primary) do
    ([{problem.function_definition, "function is defined here"}] ++
       Enum.map(problem.candidate_equations || [], &{&1, "candidate defining equation"}))
    |> Enum.flat_map(fn
      {%Span{} = span, message} when span != primary -> [%Label{span: span, style: :secondary, message: message}]
      _ -> []
    end)
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
    Suggest.rank(candidates, spelling, namespace, opts)
  end

  defp suggestion_name(%{name: name, owner: owner, imported: false}) when not is_nil(owner),
    do: "#{name_to_string(owner)}.#{name}"

  defp suggestion_name(%{name: name}), do: name

  defp namespace_title(:value), do: "value"
  defp namespace_title(:constructor), do: "constructor"
  defp namespace_title(:type), do: "type"
  defp namespace_title(:module), do: "module"
  defp namespace_title(:member), do: "module member"
  defp namespace_title(:interface), do: "interface"
  defp namespace_title(other), do: to_string(other)

  defp type_problem_title(%ExpectationOrigin{kind: :annotation}), do: "Annotation does not match"
  defp type_problem_title(%ExpectationOrigin{kind: :local_fact}), do: "Local fact does not match"
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
  defp syntax_problem_title(%SyntaxProblem{kind: :macro_literal_capture}), do: "Macro literal capture is invalid"
  defp syntax_problem_title(%SyntaxProblem{kind: :non_associative}), do: "Operator chain needs parentheses"
  defp syntax_problem_title(%SyntaxProblem{kind: :ambiguous_precedence}), do: "Operator precedence is ambiguous"
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

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_literal_capture, expected: expected}),
    do: "This macro capture must match the literal shape `#{syntax_name(expected)}`."

  defp syntax_problem_context(%SyntaxProblem{kind: :non_associative, context: %{operator: operator}}),
    do: "The `#{syntax_name(operator)}` operator cannot be chained without parentheses."

  defp syntax_problem_context(%SyntaxProblem{kind: :ambiguous_precedence}),
    do: "These operators have no declared relative precedence; add parentheses to choose the grouping."

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

  defp computed_macro_reason({:invalid_generated_syntax, {_reason, path}}),
    do: "invalid macro expansion at #{format_syntax_path(path)}"

  defp computed_macro_reason({:author_diagnostics, diagnostics}) when is_list(diagnostics),
    do: "macro rejected expansion: it reported #{length(diagnostics)} diagnostic(s)"

  defp computed_macro_reason({:author_failure, name, args}) when is_list(args),
    do: "macro rejected expansion: the macro reported `#{name}`"

  defp computed_macro_reason(_reason), do: "the generated expansion was rejected by the compiler"

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

  defp type_problem_context(%ExpectationOrigin{kind: :local_fact, owner: owner}),
    do: "The evidence for local fact `#{name_to_string(owner)}` does not match its stated type."

  defp type_problem_context(%ExpectationOrigin{kind: :call_result, owner: owner}),
    do: "The result of `#{name_to_string(owner || "this call")}` does not match the surrounding expectation."

  defp type_problem_context(%ExpectationOrigin{kind: :branch}),
    do: "Every branch of this expression must produce the same type."

  defp type_problem_context(%ExpectationOrigin{kind: :condition}),
    do: "A condition must produce `Bool` before either branch can run."

  defp type_problem_context(%ExpectationOrigin{kind: :call_argument, index: index, owner: owner}),
    do: "Argument #{display_index(index)} of `#{name_to_string(owner || "this function")}` has an incompatible type."

  defp type_problem_context(%ExpectationOrigin{kind: :application, owner: owner}),
    do: "This application of `#{name_to_string(owner || "this function")}` has an incompatible type."

  defp type_problem_context(%ExpectationOrigin{kind: :overload, owner: owner}),
    do: "The overloaded call `#{name_to_string(owner || "this function")}` has no compatible type."

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
  defp type_problem_label(%ExpectationOrigin{kind: :local_fact}), do: "this evidence has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :call_result}), do: "this call result has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :branch}), do: "this branch disagrees with another branch"
  defp type_problem_label(%ExpectationOrigin{kind: :call_argument}), do: "this argument has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :application}), do: "this application has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :overload}), do: "this overloaded call has no matching type"
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
  defp type_problem_label(%ExpectationOrigin{kind: :operator_operand}), do: "this operator operand has the wrong type"
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
