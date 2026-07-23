defmodule Cure.Diagnostic.Adapter do
  @moduledoc "Converts phase-specific and legacy error values into shared diagnostics."

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    DefiningEquationProblem,
    ExpectationOrigin,
    InductionProblem,
    Label,
    ProvenanceFrame,
    ProofChainMismatchProblem,
    ProofChainSyntaxProblem,
    RewriteProblem,
    SimplificationProblem,
    Span,
    Suggestion,
    SyntaxProblem,
    TextEdit,
    TypeProblem
  }

  alias Cure.Diagnostic.Adapter.Codegen
  alias Cure.Diagnostic.Adapter.Kernel, as: KernelAdapter
  alias Cure.Diagnostic.Adapter.Name, as: NameAdapter
  alias Cure.Diagnostic.Adapter.Operational
  alias Cure.Diagnostic.Adapter.StaticAnalysis
  alias Cure.Diagnostic.Adapter.Type, as: TypeAdapter
  alias Cure.Diagnostic.Suggest
  alias Cure.MetaAST.Metadata

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

  def from_error({:unknown_erasure_class, _name, _class} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:erases_on_non_opaque, _name} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:non_strictly_positive, _family} = error, opts),
    do: KernelAdapter.from_error(error, opts)

  def from_error({:erased_used_relevantly, details} = error, opts) when is_map(details),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:usage_violation, details} = error, opts) when is_map(details),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({kind, name}, opts)
      when kind in [
             :duplicate_type,
             :duplicate_ctor,
             :duplicate_constructor,
             :duplicate_field,
             :duplicate_parameter,
             :duplicate_index,
             :reserved_union_type_name,
             :constructor_function_collision,
             :duplicate_definition
           ] do
    if is_map(name) do
      declaration_conflict(kind, name, opts)
    else
      declaration_conflict(kind, %{name: name}, opts)
    end
  end

  def from_error({kind, %{name: _name} = details}, opts)
      when kind in [:duplicate_parameter, :duplicate_field, :duplicate_index] do
    declaration_conflict(kind, details, opts)
  end

  def from_error({:overlapping_overload, name, arity}, opts) do
    declaration_conflict(:overlapping_overload, %{name: name, arity: arity}, opts)
  end

  def from_error({:overlapping_overload, %{name: name, first: first, second: second} = details}, opts) do
    name = name_to_string(name)
    first_signature = overload_declaration_signature(name, first)
    second_signature = overload_declaration_signature(name, second)
    primary_span = Map.get(second, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(first, :span) do
        %Span{} = span when span != primary_span ->
          [pickup_label(span, :secondary, "the first indistinguishable `#{name}` overload is here")]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Overloads of `#{name}` cannot be distinguished",
      body:
        Doc.paragraph(
          "Both declarations accept the same parameter types and required argument labels. A call cannot provide enough information to choose between them."
        ),
      primary: pickup_label(primary_span, :primary, "this overload has the same callable signature as the first"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Change a parameter type or required argument label, or rename one function",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :overlapping_overload,
        name: name,
        arity: Map.get(details, :arity),
        first_signature: first_signature,
        second_signature: second_signature,
        first_id: name_to_string(Map.get(first, :id, name)),
        second_id: name_to_string(Map.get(second, :id, name))
      }
    )
  end

  def from_error({:overlapping_instance, interface, head}, opts) do
    declaration_conflict(:overlapping_instance, %{interface: interface, head: head}, opts)
  end

  def from_error({:overlapping_instance, %{interface: interface, head: canonical_head} = details}, opts) do
    interface = name_to_string(interface)
    head = name_to_string(Map.get(details, :second_for) || Cure.Elab.Name.base(canonical_head))
    primary_span = Map.get(details, :second_span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(details, :first_span) do
        %Span{} = span when span != primary_span ->
          [pickup_label(span, :secondary, "the first `#{interface}` implementation for `#{head}` is here")]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementations overlap",
      body:
        Doc.paragraph(
          "There are two anonymous implementations of `#{interface}` for `#{head}`. Cure requires one globally coherent implementation so every call selects the same behavior."
        ),
      primary: pickup_label(primary_span, :primary, "this second implementation conflicts with the first"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Remove one implementation, or give one an `as` name and select it explicitly",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :overlapping_instance,
        interface: interface,
        head: head,
        head_id: name_to_string(canonical_head)
      }
    )
  end

  def from_error({:overlapping_named_instance, name, interface, head}, opts) do
    declaration_conflict(
      :overlapping_named_instance,
      %{name: name, interface: interface, head: head},
      opts
    )
  end

  def from_error({:overlapping_named_instance, %{name: name} = details}, opts) do
    name = name_to_string(name)
    first_interface = name_to_string(Map.get(details, :first_interface, "an interface"))
    second_interface = name_to_string(Map.get(details, :interface, "an interface"))
    first_head = name_to_string(Map.get(details, :first_for, Cure.Elab.Name.base(Map.get(details, :first_head))))
    second_head = name_to_string(Map.get(details, :second_for, Cure.Elab.Name.base(Map.get(details, :head))))
    primary_span = Map.get(details, :second_span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(details, :first_span) do
        %Span{} = span when span != primary_span ->
          [pickup_label(span, :secondary, "`#{name}` first names `#{first_interface}` for `#{first_head}` here")]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation name is already used",
      body:
        Doc.paragraph(
          "The name `#{name}` already selects `#{first_interface}` for `#{first_head}`, so it cannot also select `#{second_interface}` for `#{second_head}`. Named implementations must have distinct names wherever they are in scope."
        ),
      primary: pickup_label(primary_span, :primary, "this second `#{name}` conflicts with the first"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Choose a different name after `as` for one implementation",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :overlapping_named_instance,
        name: name,
        first_interface: first_interface,
        first_head: first_head,
        second_interface: second_interface,
        second_head: second_head
      }
    )
  end

  def from_error({:sibling_module_collision, name, owners}, opts) do
    declaration_conflict(:sibling_module_collision, %{name: name, owners: owners}, opts)
  end

  def from_error({:sibling_module_collision, %{name: _name} = details}, opts) do
    declaration_conflict(:sibling_module_collision, details, opts)
  end

  def from_error({:precedence_cycle, %{groups: groups} = details}, opts) when is_list(groups) do
    operator_conflict(:precedence_cycle, details, opts)
  end

  def from_error({:precedence_cycle, groups}, opts) when is_list(groups) do
    operator_conflict(:precedence_cycle, %{groups: groups}, opts)
  end

  def from_error({:conflicting_operator_fixity, details}, opts) when is_map(details) do
    operator_conflict(:conflicting_operator_fixity, details, opts)
  end

  def from_error({:conflicting_precedence_group, details}, opts) when is_map(details) do
    operator_conflict(:conflicting_precedence_group, details, opts)
  end

  def from_error({:unsupported_operand_type, _operator} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:no_operator_meaning, _operator} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:cannot_infer_match_type, %{reason: reason}} = error, opts)
      when reason in [:no_constructor_arm, :scrutinee_not_data],
      do: TypeAdapter.from_error(error, opts)

  def from_error({:cannot_infer_match_type, _legacy_expression} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:lambda_expected_pi, %{expected: _expected}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:lambda_expected_pi, _expected} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:unsupported_async, message, meta}, opts)
      when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E107",
      key: :unsupported_async,
      severity: :error,
      title: "Unsupported asynchronous primitive",
      body: Doc.paragraph(message),
      primary: primary_label(opts, "use a supported asynchronous boundary"),
      payload: %{primitive: :unknown, stage: :runtime}
    )
  end

  def from_error({:unsupported_async, %{primitive: primitive} = details}, opts) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E107",
      key: :unsupported_async,
      severity: :error,
      title: "`#{name_to_string(primitive)}` is unavailable in dependent code",
      body:
        Doc.paragraph(
          "The dependent runtime cannot lower `#{name_to_string(primitive)}` while preserving Cure's checked process and message types. This is a runtime capability boundary, not a type error in the spawned expression."
        ),
      primary: pickup_label(span, :primary, "this asynchronous operation has no dependent-runtime lowering"),
      suggestions: [
        %Suggestion{
          message: "Use an actor, FSM, or supervisor declaration for managed concurrency",
          applicability: :manual
        }
      ],
      payload: %{
        primitive: primitive,
        stage: Map.get(details, :stage, :dependent_runtime),
        capability: :managed_concurrency
      }
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
      payload: %{form: tag, stage: :elaboration}
    )
  end

  def from_error({:splice_outside_quote, %{form: tag} = details}, opts)
      when tag in [:splice, :splice_group] do
    form = if tag == :splice_group, do: "$(expressions ...)", else: "$(expression)"
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E108",
      key: :splice_outside_quote,
      severity: :error,
      title: "Splice has no enclosing quote",
      body:
        Doc.paragraph(
          "`#{form}` inserts syntax into a surrounding `quote`, but this splice is in ordinary expression code. There is no quoted syntax tree here to receive its value."
        ),
      primary: pickup_label(span, :primary, "this splice is outside every `quote`"),
      suggestions: [
        %Suggestion{
          message: "Move this splice inside `quote ...`, or remove `$()` to evaluate an ordinary expression",
          applicability: :manual
        }
      ],
      payload: %{form: tag, stage: Map.get(details, :stage, :elaboration)}
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

  def from_error({:simplification_failed, %SimplificationProblem{} = problem}, opts) do
    {title, message, label} =
      case problem.kind do
        :inadmissible_rule ->
          {"Simplification rule is not admissible", "This rule cannot be given a deterministic decreasing orientation.",
           "this rule cannot be admitted"}

        :proof_mismatch ->
          {"Simplified proof does not match", "The supplied proof and current goal simplify to different propositions.",
           "the simplified propositions still differ"}

        :resource_guard ->
          {"Simplification stopped safely",
           "The simplifier reached its explicit resource limit without claiming that the goal is false.",
           "simplification stopped at its resource limit"}

        _ ->
          {"Simplification left a residual goal",
           "The approved rules made no further progress, and the remaining proposition is not definitionally reflexive.",
           "this goal was not fully simplified"}
      end

    Diagnostic.new(
      code: "E112",
      key: :simplification_failed,
      severity: :error,
      title: title,
      body: simplification_body(message, problem, opts),
      primary: primary_label(opts, label),
      secondary: simplification_labels(problem, Keyword.get(opts, :span)),
      payload: problem
    )
  end

  def from_error({:induction_failed, %InductionProblem{} = problem}, opts) do
    {title, message, label} =
      case problem.kind do
        :non_inductive_subject ->
          {"Cannot induct over this value", "The selected subject does not have an inductive datatype.",
           "this subject is not inductive"}

        :missing_case ->
          {"Induction case is missing", "The induction block does not cover every possible constructor.",
           "add the missing constructor case"}

        :duplicate_case ->
          {"Induction case is duplicated", "A constructor may appear only once in an induction block.",
           "this constructor case is duplicated"}

        :impossible_case ->
          {"Induction case is reachable",
           "This case was marked impossible, but the subject indices permit its constructor.",
           "this constructor case is possible"}

        :unknown_case ->
          {"Unknown induction constructor", "This pattern does not name a constructor of the subject datatype.",
           "this constructor is unavailable"}

        :wrong_case_fields ->
          {"Induction case has the wrong fields",
           "Bind every ordinary constructor field, followed by one induction hypothesis for each recursive field.",
           "this constructor pattern has the wrong shape"}

        :unavailable_hypothesis ->
          {"Invalid induction hypothesis binder", "An induction hypothesis must be bound by an ordinary name.",
           "name this induction hypothesis"}

        :mistyped_hypothesis ->
          {"Induction hypothesis has the wrong proposition",
           "This induction hypothesis is specialized for its recursive field, but that proposition does not satisfy this use.",
           "this induction hypothesis has a different proposition"}

        :unknown_subject_type ->
          {"Cannot determine the induction subject type",
           "Give the local value a type annotation or induct over an expression whose result type is declared.",
           "the subject type is not available"}

        :local_subject_requires_return_annotation ->
          {"Local induction needs a declared result type",
           "Closure-lifted induction needs the enclosing proposition in order to construct its motive.",
           "declare this function's result proposition"}

        _ ->
          {"Induction could not be elaborated", "The induction block could not be lowered to checked total recursion.",
           "this induction block is invalid"}
      end

    Diagnostic.new(
      code: "E113",
      key: :induction_failed,
      severity: :error,
      title: title,
      body: Doc.paragraph(induction_message(message, problem)),
      primary: induction_primary(problem, opts, label),
      secondary: induction_labels(problem),
      suggestions: induction_suggestions(problem),
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

  def from_error({:named_argument_mismatch, variant, details}, opts) when is_map(details) do
    {title, message, label} =
      case variant do
        :unknown_label ->
          {"Unknown named argument", "`#{details.label}` is not a parameter label of this call target.",
           "this name does not match a parameter"}

        :duplicate_label ->
          {"Named argument is supplied twice", "`#{details.label}` fills a parameter that already has an argument.",
           "this parameter was already filled"}

        :positional_after_named ->
          {"Positional argument follows a named argument",
           "Positional arguments must come first; named arguments may follow in any order.",
           "move this positional argument before the named arguments"}

        :missing_label ->
          {"Required named argument is missing",
           "The parameter `#{details.label}` must be supplied by its declared argument name.",
           "write `#{details.label}:` for this argument"}

        :ambiguous_label ->
          {"Named arguments do not select one overload",
           "These names fit more than one candidate, or fail differently across the remaining candidates.",
           "make the target or argument names unambiguous"}
      end

    Diagnostic.new(
      code: "E115",
      key: :named_argument_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: named_argument_primary(details, opts, label),
      secondary: named_argument_labels(details),
      suggestions: named_argument_suggestions(variant, details),
      payload: Map.put(details, :kind, variant)
    )
  end

  def from_error({:missing_diagnosis, points}, opts), do: macro_validation_failure(:missing_diagnosis, points, opts)
  def from_error({:rule_unpinned, keywords}, opts), do: macro_validation_failure(:rule_unpinned, keywords, opts)

  def from_error({:source_context, {:missing_diagnosis, points}, context}, opts) when is_map(context),
    do: macro_validation_failure(:missing_diagnosis, points, opts, context)

  def from_error({:source_context, {:rule_unpinned, keywords}, context}, opts) when is_map(context),
    do: macro_validation_failure(:rule_unpinned, keywords, opts, context)

  def from_error({:source_context, {:example_mismatch, mismatches}, context}, opts) when is_map(context),
    do: macro_validation_failure(:example_mismatch, mismatches, opts, context)

  def from_error({:source_context, {:example_type_mismatch, failures}, context}, opts) when is_map(context),
    do: macro_validation_failure(:example_type_mismatch, failures, opts, context)

  def from_error({:source_context, {:computed_example_error, failures}, context}, opts) when is_map(context),
    do: macro_validation_failure(:computed_example_error, failures, opts, context)

  def from_error({:source_context, {:reserved_syntax_field, field, keywords}, context}, opts) when is_map(context),
    do: macro_validation_failure(:reserved_syntax_field, %{first: field, second: keywords}, opts, context)

  def from_error({:source_context, {:expansion_ill_typed, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: expansion_proof_failure(details, context, opts)

  def from_error({:source_context, {:unsupported_hole_type, category}, context}, opts) when is_map(context),
    do: macro_validation_failure(:unsupported_hole_type, %{detail: category}, opts, context)

  def from_error({:source_context, {:generated_hole_not_well_typed, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: generated_hole_invariant_failure(details, context, opts)

  def from_error({:example_mismatch, mismatches}, opts),
    do: macro_validation_failure(:example_mismatch, mismatches, opts)

  def from_error({:example_type_mismatch, failures}, opts),
    do: macro_validation_failure(:example_type_mismatch, failures, opts)

  def from_error({:computed_example_error, failures}, opts),
    do: macro_validation_failure(:computed_example_error, failures, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_packet_name,
             :invalid_packet_endian,
             :unknown_packet_scalar,
             :missing_packet_endian,
             :invalid_packet_field
           ],
      do: macro_packet_failure(kind, %{detail: detail}, opts)

  def from_error({kind, field, dependency}, opts)
      when kind in [:forward_packet_length, :invalid_packet_crc_fields],
      do: macro_packet_failure(kind, %{field: field, dependency: dependency}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_packet_field, :invalid_packet_field_name, :duplicate_packet_field],
      do: macro_packet_failure(kind, %{}, opts)

  def from_error({:invalid_driver_base, base}, opts),
    do: macro_driver_failure(:invalid_driver_base, %{base: base}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_driver_register, :duplicate_driver_register, :overlapping_driver_register],
      do: macro_driver_failure(kind, %{}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_board_name,
             :invalid_board_chip,
             :unknown_board_pin,
             :invalid_board_capability,
             :invalid_board_bus,
             :unknown_bus_pin,
             :missing_bus_capability
           ],
      do: macro_board_failure(kind, %{detail: detail}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_board_definition,
             :missing_board_chip,
             :invalid_board_pins,
             :invalid_board_capabilities,
             :invalid_board_buses,
             :invalid_board_flash,
             :flash_offset_out_of_bounds
           ],
      do: macro_board_failure(kind, %{}, opts)

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

  def from_error({:codegen_error, {:implementation_scope, _} = reason}, opts), do: from_error(reason, opts)

  def from_error({:codegen_error, {:sibling_module_collision, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {kind, _} = reason}, opts)
      when kind in [
             :duplicate_type,
             :duplicate_ctor,
             :duplicate_constructor,
             :duplicate_field,
             :duplicate_parameter,
             :duplicate_index,
             :reserved_union_type_name,
             :constructor_function_collision,
             :duplicate_definition
           ],
      do: from_error(reason, opts)

  def from_error({:codegen_error, {kind, _} = reason}, opts)
      when kind in [
             :proof_chain_mismatch,
             :rewrite_failed,
             :simplification_failed,
             :induction_failed,
             :defining_equation_unavailable
           ],
      do: from_error(reason, opts)

  def from_error({:codegen_error, {:named_argument_mismatch, _, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_error, {:proof_shape_mismatch, _, _} = reason}, opts),
    do: from_error(reason, opts)

  def from_error({:codegen_failure, details}, opts) when is_map(details) do
    Codegen.from_error({:codegen_failure, details}, opts)
  end

  def from_error({:codegen_error, reason}, opts), do: Codegen.from_error({:codegen_error, reason}, opts)

  def from_error({:parse_error, [reason | _]}, opts), do: from_error(reason, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_sub_union, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_literal_member, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_as, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_nested, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_tuple, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :shadowed_tuple_arg, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: reason, name: _name} = details}, context},
        opts
      )
      when reason in [:shadowed_catchall, :shadowed_literal_catchall, :shadowed_default] and is_map(context),
      do: shadowed_sub_union_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :named_default_nonvariable, name: _name} = details},
         context},
        opts
      )
      when is_map(context),
      do: named_default_nonvariable_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :default_in_with, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: with_default_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_pattern, %{reason: :unlowered_nested_constructor_argument} = details}, context},
        opts
      )
      when is_map(context),
      do: unlowered_nested_constructor_failure(details, context, opts)

  def from_error({:source_context, {:unsupported_pattern, shape}, context}, opts) when is_map(context) do
    from_error(
      %SyntaxProblem{
        kind: :unrecognized_pattern,
        observed: shape,
        at: Keyword.get(opts, :span, Map.get(context, :span)),
        context: context
      },
      opts
    )
  end

  def from_error({:source_context, {:unsupported_guard, :non_exhaustive}, context}, opts)
      when is_map(context),
      do: non_exhaustive_guard_failure(context, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :shadowed, name: _name} = details}, context},
        opts
      )
      when is_map(context),
      do: shadowed_guard_binding_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :refutable_pattern} = details}, context},
        opts
      )
      when is_map(context),
      do: refutable_guard_pattern_failure(details, context, opts)

  def from_error(
        {:source_context, {:unsupported_guard, %{reason: :complex_scrutinee} = details}, context},
        opts
      )
      when is_map(context),
      do: complex_guard_scrutinee_failure(details, context, opts)

  def from_error({:source_context, {:unsolved_metavariables, name}, context}, opts) when is_map(context) do
    cond do
      Map.get(context, :constructor_result_mismatch) ->
        checked_constructor_result_failure(name, context, opts)

      Map.get(context, :expectation_origin) == :constructor_argument ->
        nested_constructor_implicit_failure(name, context, opts)

      true ->
        opts = Keyword.put_new(opts, :span, Map.get(context, :span))
        primary = primary_label(opts, "these hidden arguments cannot be inferred")

        secondary =
          case {Map.get(context, :expectation_span), primary} do
            {%Span{} = span, %Label{span: primary_span}} when span != primary_span ->
              [%Label{span: span, style: :secondary, message: "this result annotation still leaves them unknown"}]

            _ ->
              []
          end

        Diagnostic.new(
          code: "E011",
          key: :missing_implicit_argument,
          severity: :error,
          title: "Missing implicit argument",
          body:
            Doc.stack([
              Doc.paragraph("Cure could not infer every implicit argument for `#{name}` at this call site."),
              Doc.paragraph(
                "The call leaves hidden type or index values unconstrained. Provide arguments that determine them, or use the result where its dependent type is known."
              )
            ]),
          primary: primary,
          secondary: secondary,
          suggestions: [
            %Suggestion{
              message: "Provide arguments or a result type that determines the hidden values",
              applicability: :manual
            }
          ],
          payload: Map.put(context, :name, name)
        )
    end
  end

  def from_error({:source_context, {:no_instance, _interface, _head}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:ambiguous_method, method, interfaces}, context}, opts)
      when is_map(context),
      do: ambiguous_member(method, interfaces, context, opts)

  def from_error({:source_context, {:inconsistent_head_kind, interface}, context}, opts)
      when is_map(context),
      do: inconsistent_interface_head(interface, context, opts)

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

  def from_error({:source_context, {:missing_branch, _branch}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error(
        {:source_context, {:tuple_missing_branch, %{branch: _branch}}, context} = error,
        opts
      )
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, :branch_type, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:branch_type, _details}, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:reachable_impossible, _branch}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:duplicate_branch, _branch}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error(
        {:source_context, {:forced_pattern_mismatch, actual, expected}, %{forced_pattern_span: _} = context},
        opts
      ) do
    forced_pattern_mismatch_failure(actual, expected, context, opts)
  end

  def from_error({:source_context, {:forced_pattern_mismatch, actual, expected}, context}, opts)
      when is_map(context) do
    pattern_problem(:forced_pattern_mismatch, %{actual: actual, expected: expected}, context, opts)
  end

  def from_error(
        {:source_context, {:named_implicit_unforced, name}, %{named_implicit_status: :unforced} = context},
        opts
      ),
      do: named_implicit_unforced_failure(name, context, opts)

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
    if rematch_context_enriched?(context) do
      rematch_pattern_failure(kind, %{original: first, restated: second}, context, opts)
    else
      pattern_problem(kind, %{actual: first, expected: second}, context, opts)
    end
  end

  def from_error({:source_context, {kind, details}, context}, opts)
      when kind in [
             :with_rematch_ctor_mismatch,
             :with_rematch_non_constructor_pattern,
             :with_rematch_inconsistent_binding,
             :with_rematch_unsupported_parent_pattern
           ] and
             is_map(context) do
    if rematch_context_enriched?(context) do
      rematch_pattern_failure(kind, %{details: details}, context, opts)
    else
      if kind == :with_rematch_unsupported_parent_pattern do
        contextual_type_failure(kind, %{detail: details}, opts)
      else
        pattern_problem(kind, %{details: details}, context, opts)
      end
    end
  end

  def from_error(
        {:source_context, {:with_rematch_arity_mismatch, expected, actual}, context},
        opts
      )
      when is_map(context),
      do: rematch_pattern_failure(:with_rematch_arity_mismatch, %{expected: expected, actual: actual}, context, opts)

  def from_error({:source_context, {:unknown_record, name, candidates}, context}, opts)
      when is_map(context) and is_list(candidates),
      do: unknown_record_failure(name, candidates, context, opts)

  def from_error({:source_context, {:unknown_record, name}, context}, opts) when is_map(context),
    do: unknown_record_failure(name, Map.get(context, :available_records, []), context, opts)

  def from_error({:source_context, {:unknown_field, _record, _field}, context} = error, opts)
      when is_map(context),
      do: NameAdapter.from_error(error, opts)

  def from_error({:source_context, {:unknown_field, record, field, available_fields}, context}, opts)
      when is_map(context) and is_list(available_fields) do
    NameAdapter.from_error({:source_context, {:unknown_field, record, field, available_fields}, context}, opts)
  end

  def from_error({:source_context, {:projection_not_a_record, record}, context}, opts) when is_map(context) do
    projection_receiver_failure(record, context, opts)
  end

  def from_error(
        {:source_context, {:dependent_record_projection, record, field}, context},
        opts
      )
      when is_map(context),
      do: dependent_record_projection_failure(record, field, context, opts)

  def from_error({:unknown_field, _record, _field} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_field, _record, _field, available_fields} = error, opts)
      when is_list(available_fields),
      do: NameAdapter.from_error(error, opts)

  def from_error({:source_context, {:projection_non_record, field}, context}, opts) when is_map(context) do
    projection_receiver_failure(nil, Map.put_new(context, :field, field), opts)
  end

  def from_error({:unknown_record, name}, opts),
    do: from_error({:source_context, {:unknown_record, name}, %{}}, opts)

  def from_error({:unknown_record, name, candidates}, opts) when is_list(candidates),
    do: from_error({:source_context, {:unknown_record, name, candidates}, %{}}, opts)

  def from_error({:source_context, {:record_field_mismatch, name}, context}, opts)
      when is_map(context) and not is_map(name) do
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

  def from_error({:source_context, {:record_field_mismatch, details}, context}, opts)
      when is_map(details) and is_map(context) do
    unknown = Map.get(details, :unknown, [])
    missing = Map.get(details, :missing, [])
    declared = Map.get(details, :declared, [])
    record = Map.get(details, :record)
    field_spans = Map.get(context, :field_spans, %{})
    offending = List.first(unknown)
    field_span = Map.get(field_spans, offending) || Map.get(field_spans, name_to_string(offending))
    record_name_span = Map.get(context, :record_name_span)
    closer_span = Map.get(context, :closer_span)
    primary_span = if(offending, do: field_span, else: closer_span || Map.get(context, :span))

    opts =
      if primary_span do
        Keyword.put(opts, :span, primary_span)
      else
        Keyword.put_new(opts, :span, Map.get(context, :span))
      end

    candidates = record_field_candidates(offending, declared, record)
    unique_candidate = unique_record_field_candidate(offending, candidates)

    body =
      cond do
        offending && unique_candidate ->
          Doc.paragraph(
            "`#{name_to_string(offending)}` is not a field of `#{name_to_string(record)}`. Did you mean `#{unique_candidate.name}`?"
          )

        offending ->
          Doc.paragraph(
            "`#{name_to_string(offending)}` is not a field of `#{name_to_string(record)}`. Available fields are #{field_list(declared)}."
          )

        missing != [] ->
          Doc.paragraph("This `#{name_to_string(record)}` value is missing #{field_list(missing)}.")

        true ->
          Doc.paragraph("The supplied fields do not match `#{name_to_string(record)}`.")
      end

    suggestions =
      if offending do
        record_field_suggestions(offending, candidates, field_span)
      else
        missing_record_field_suggestions(missing)
      end

    operation = Map.get(context, :expectation_origin)

    secondary =
      [
        record_operation_label(record_name_span, primary_span, record, operation),
        record_update_base_label(Map.get(context, :base_span), primary_span, operation)
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E022",
      key: :record_field_mismatch,
      severity: :error,
      title: if(offending, do: "Unknown record field", else: "Missing record field"),
      body: body,
      primary:
        primary_label(
          opts,
          if(offending,
            do: "this field is not declared by the record",
            else: "add #{missing_field_label(missing)} before this closing brace"
          )
        ),
      secondary: secondary,
      suggestions: suggestions,
      payload: %{
        record: record,
        declared: declared,
        provided: Map.get(details, :provided, []),
        unknown: unknown,
        missing: missing,
        candidates: candidates,
        checking: Map.get(context, :checking),
        operation: operation
      }
    )
  end

  def from_error({:source_context, {:record_update_base_mismatch, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: record_update_base_failure(details, context, opts)

  def from_error({:source_context, {:foreign_ctor, constructor}, context}, opts)
      when is_map(context),
      do: NameAdapter.from_error({:source_context, {:foreign_ctor, constructor}, context}, opts)

  def from_error({:source_context, {kind, _name}, context} = error, opts)
      when kind in [:unknown_ctor, :foreign_ctor, :unknown_pattern_constructor, :unknown_family] and
             is_map(context),
      do: NameAdapter.from_error(error, opts)

  def from_error({:no_such_interface, _interface} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_interface_method, _interface, _method} = error, opts),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_interface_method, details} = error, opts) when is_map(details),
    do: NameAdapter.from_error(error, opts)

  def from_error({:implementation_scope, %{kind: :member_outside} = details}, opts) do
    implementation = "#{name_to_string(details.interface)} for #{name_to_string(details.for)}"
    primary_span = Map.get(details, :member_span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(details, :implementation_span) do
        %Span{} = span ->
          [%Label{span: span, style: :secondary, message: "this implementation has no nested members"}]

        _ ->
          []
      end

    suggestions =
      case Map.get(details, :insertion_span) do
        %Span{} = span ->
          [
            %Suggestion{
              message: "Indent `#{name_to_string(details.member)}` beneath the implementation",
              applicability: :machine_applicable,
              edits: [%TextEdit{span: span, replacement: Map.get(details, :indentation, "  ")}]
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E116",
      key: :implementation_scope,
      severity: :error,
      title: "Implementation member is outside its implementation scope",
      body:
        Doc.paragraph(
          "`#{name_to_string(details.member)}` appears to implement `#{implementation}`, but it is aligned outside that implementation. Implementation members must be indented beneath their `implementation` declaration."
        ),
      primary:
        primary_label(
          Keyword.put(opts, :span, primary_span),
          "indent this member so it belongs to the implementation"
        ),
      secondary: secondary,
      suggestions: suggestions,
      payload: details
    )
  end

  def from_error({:implementation_scope, %{kind: :empty} = details}, opts) do
    span = Map.get(details, :implementation_span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E116",
      key: :implementation_scope,
      severity: :error,
      title: "Implementation has no members",
      body:
        Doc.paragraph(
          "The implementation of `#{name_to_string(details.interface)}` for `#{name_to_string(details.for)}` is empty. Every implementation must contain at least one nested member."
        ),
      primary:
        primary_label(
          Keyword.put(opts, :span, span),
          "add the implementation's members beneath this declaration"
        ),
      suggestions: [
        %Suggestion{
          message: "Add and indent the required interface members beneath this implementation",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:missing_method, interface, method}, opts),
    do: interface_failure(:missing_method, %{interface: interface, method: method}, opts)

  def from_error({:missing_method, %{interface: interface, method: method} = details}, opts) do
    interface = name_to_string(interface)
    method = name_to_string(method)

    head =
      details
      |> Map.get(:for, Cure.Elab.Name.base(Map.get(details, :head)) || "this type")
      |> name_to_string()

    head_id = name_to_string(Map.get(details, :head, head))
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation is missing `#{method}`",
      body:
        Doc.paragraph(
          "`#{interface}` requires a method named `#{method}`, but this implementation for `#{head}` does not provide it and the interface has no default implementation."
        ),
      primary: pickup_label(span, :primary, "add `#{method}` beneath this implementation"),
      suggestions: [
        %Suggestion{
          message: "Implement `#{method}` with the signature required by `#{interface}`",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :missing_method,
        interface: interface,
        method: method,
        head: head,
        head_id: head_id
      }
    )
  end

  def from_error({:method_signature_mismatch, interface, method}, opts),
    do: interface_failure(:method_signature_mismatch, %{interface: interface, method: method}, opts)

  def from_error({:method_signature_mismatch, %{interface: _interface, method: _method} = details}, opts),
    do: method_signature_failure(details, opts)

  def from_error({:instance_head_ill_formed, %{reason: reason} = details}, opts) do
    interface = name_to_string(Map.get(details, :interface, "this interface"))
    authored_head = name_to_string(Map.get(details, :for, "this expression"))
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    {explanation, label, hint} =
      case reason do
        :not_type_head ->
          {
            "`#{authored_head}` is a value, but an implementation can only be declared for a type. Cure needs a type constructor here so it can select this implementation consistently.",
            "this is a value, not an implementation type",
            "Replace `#{authored_head}` with the name of a type that implements `#{interface}`"
          }

        :lowering_failed ->
          {
            "Cure could not interpret `#{authored_head}` as a type for this `#{interface}` implementation.",
            "this implementation head is not a valid type",
            "Use a well-formed type after `for`"
          }
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation head is not a type",
      body: Doc.paragraph(explanation),
      primary: pickup_label(span, :primary, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :instance_head_ill_formed,
        reason: reason,
        interface: interface,
        authored_head: authored_head
      }
    )
  end

  def from_error({:instance_head_ill_formed, reason}, opts),
    do: interface_failure(:instance_head_ill_formed, %{reason: reason}, opts)

  def from_error({:missing_superinterface, interface, super_interface, head}, opts),
    do:
      interface_failure(
        :missing_superinterface,
        %{interface: interface, superinterface: super_interface, head: head},
        opts
      )

  def from_error(
        {:missing_superinterface,
         %{interface: interface, superinterface: super_interface, head: canonical_head} = details},
        opts
      ) do
    interface = name_to_string(interface)
    super_interface = name_to_string(super_interface)
    head = name_to_string(Map.get(details, :for, Cure.Elab.Name.base(canonical_head)))
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Required implementation is missing",
      body:
        Doc.paragraph(
          "`#{interface}` requires `#{super_interface}`, so implementing `#{interface}` for `#{head}` also requires an implementation of `#{super_interface}` for `#{head}`."
        ),
      primary:
        pickup_label(
          span,
          :primary,
          "this implementation also needs `#{super_interface}` for `#{head}`"
        ),
      suggestions: [
        %Suggestion{
          message: "Add `implementation #{super_interface} for #{head}`",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :missing_superinterface,
        interface: interface,
        superinterface: super_interface,
        head: head,
        head_id: name_to_string(canonical_head)
      }
    )
  end

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

  def from_error({:source_context, {:non_strictly_positive, _constructor}, context} = error, opts)
      when is_map(context),
      do: KernelAdapter.from_error(error, opts)

  def from_error({:source_context, {:erased_used_relevantly, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:usage_violation, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:totality_required, _name}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:compile_time_totality, _name, _reason}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:final_core_violation, name, rejections}, context}, opts)
      when is_list(rejections) and is_map(context) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(context, :span))
      |> Keyword.put(:codegen_stage, Map.get(context, :codegen_stage, :final_core_validation))
      |> Keyword.put(:codegen_module, Map.get(context, :codegen_module))

    Codegen.from_error({:final_core_violation, name, rejections}, opts)
  end

  def from_error(
        {:source_context, {:unsupported_expression, {:hole, meta, _children}}, context},
        opts
      )
      when is_list(meta) and is_map(context) do
    inferred_hole_failure(Keyword.get(meta, :name), context, opts)
  end

  def from_error({:source_context, {kind, _operator}, context} = error, opts)
      when kind in [:unsupported_operand_type, :no_operator_meaning] and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {kind, _detail}, context} = error, opts)
      when kind in [
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :unreachable_after_default_pattern
           ] and
             is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {kind}, context} = error, opts)
      when kind in [:binary_match_needs_default, :map_match_needs_default] and is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {kind, detail}, context}, opts)
      when kind in [
             :unsupported_comprehension_pattern,
             :unsupported_binary_generator_pattern,
             :unsupported_binary_segment,
             :unsupported_binary_match_arm,
             :unsupported_map_match_arm,
             :unsupported_map_value_pattern,
             :unsupported_map_key_pattern,
             :unsupported_block_statement,
             :unsupported_block
           ] and is_map(context) do
    span = surface_detail_span(detail) || Map.get(context, :span)
    surface_structure_failure(kind, detail, Keyword.put(opts, :span, span))
  end

  def from_error({:source_context, {:primitive_missing_builtin, name}, context}, opts)
      when is_map(context),
      do: primitive_declaration_failure(:missing_builtin, %{name: name}, context, opts)

  def from_error({:source_context, {:unknown_primitive_tag, tag}, context}, opts)
      when is_map(context),
      do: primitive_declaration_failure(:unknown_builtin, %{tag: tag}, context, opts)

  def from_error(
        {:source_context, {:primitive_floor_mismatch, name, declared, expected}, context},
        opts
      )
      when is_map(context),
      do:
        primitive_declaration_failure(
          :floor_mismatch,
          %{name: name, declared: primitive_core_tag(declared), expected: primitive_core_tag(expected)},
          context,
          opts
        )

  def from_error({:source_context, {:unsupported_declaration, shape}, context}, opts)
      when is_map(context),
      do: primitive_declaration_failure(:unsupported_declaration, %{shape: shape}, context, opts)

  def from_error({:source_context, {:extern_returns_union, name, codomain}, context}, opts)
      when is_map(context),
      do: extern_union_failure(:nested, name, codomain, context, opts)

  def from_error({:source_context, {:extern_union_indistinct, name, reason}, context}, opts)
      when is_map(context),
      do: extern_union_failure(:indistinct, name, reason, context, opts)

  def from_error({:source_context, {:bounded_lit_out_of_range, value, bound}, context}, opts)
      when is_map(context),
      do: bounded_literal_failure(value, bound, context, opts)

  def from_error(
        {:source_context, {:cannot_infer_dependent_match, _inferred_type}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, {:result_type_not_family, family}, context}, opts)
      when is_map(context),
      do: constructor_result_family_failure(family, context, opts)

  def from_error(
        {:source_context, {:typed_pattern_type_mismatch, _type_ast}, %{field_type: field_type} = context},
        opts
      )
      when not is_nil(field_type),
      do: typed_pattern_annotation_failure(context, opts)

  def from_error(
        {:source_context, {:typed_pattern_arity, _position}, %{visible_arity: _} = context},
        opts
      ),
      do: typed_pattern_arity_failure(context, opts)

  def from_error(
        {:source_context, {:forced_pattern_not_in_pattern, _meta},
         %{forced_pattern_position: :positional_constructor_argument} = context},
        opts
      ),
      do: positional_forced_pattern_failure(context, opts)

  def from_error({:source_context, {:applied_non_function, details}, context} = error, opts)
      when is_map(details) and is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:telescope_index_out_of_bounds, index, arity}, context},
        opts
      )
      when is_integer(index) and is_integer(arity) and is_map(context),
      do: telescope_index_failure(index, arity, context, opts)

  def from_error({:source_context, {:unknown_erasure_class, _name, _class}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:erases_on_non_opaque, _name}, context} = error, opts)
      when is_map(context),
      do: StaticAnalysis.from_error(error, opts)

  def from_error({:source_context, {:effect_binder_erased, details}, context}, opts)
      when is_map(details) and is_map(context),
      do: erased_effect_binder_failure(details, context, opts)

  def from_error({:source_context, {:forced_pattern_not_in_pattern, _meta}, context}, opts)
      when is_map(context),
      do: pattern_only_syntax(:forced_pattern, context, opts)

  def from_error({:source_context, {:named_implicit_not_in_pattern, _meta}, context}, opts)
      when is_map(context),
      do: pattern_only_syntax(:named_implicit_pattern, context, opts)

  def from_error({:source_context, kind, context}, opts)
      when kind in [:rewrite_requires_expected_type, :rewrite_proof_not_equality] and is_map(context),
      do: rewrite_failure(kind, context, opts)

  def from_error({:source_context, :with_mixed_rematch_arms, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, :with_scrutinee_not_data, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error({:source_context, :match_scrutinee_not_data, context} = error, opts)
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:with_indexed_scrutinee_unsupported, _family}, context} = error,
        opts
      )
      when is_map(context),
      do: TypeAdapter.from_error(error, opts)

  def from_error(
        {:source_context, {:with_sibling_dependency_unsupported, reason}, context},
        opts
      )
      when reason in [:sibling_references_sibling, :kept_references_sibling] and
             is_map(context) do
    if Map.has_key?(context, :dependent) do
      with_sibling_dependency_failure(
        %{
          reason: reason,
          dependent: Map.get(context, :dependent),
          dependency: Map.get(context, :dependency)
        },
        context,
        opts
      )
    else
      contextual_type_failure(:with_sibling_dependency_unsupported, %{detail: reason}, opts)
    end
  end

  def from_error({:source_context, {:rewrite_no_match, _left, _right}, context}, opts)
      when is_map(context),
      do: rewrite_failure(:rewrite_no_match, context, opts)

  def from_error({:source_context, {:rewrite_no_match, _left, _right, _goal}, context}, opts)
      when is_map(context),
      do: rewrite_failure(:rewrite_no_match, context, opts)

  def from_error({:source_context, {:cannot_derive, interface}, context}, opts)
      when is_map(context),
      do: deriving_failure(:cannot_derive, %{interface: interface}, context, opts)

  def from_error({:source_context, {:deriving_needs_strings, interface}, context}, opts)
      when is_map(context),
      do: deriving_failure(:deriving_needs_strings, %{interface: interface}, context, opts)

  def from_error({:source_context, {:deriving_needs_constraints, interface, type_name}, context}, opts)
      when is_map(context),
      do: deriving_failure(:deriving_needs_constraints, %{interface: interface, type: type_name}, context, opts)

  def from_error({:source_context, {:cannot_derive_shape, interface, type_name}, context}, opts)
      when is_map(context),
      do: deriving_failure(:cannot_derive_shape, %{interface: interface, type: type_name}, context, opts)

  def from_error({:source_context, {:cannot_derive_method, interface, method, reason}, context}, opts)
      when is_map(context),
      do:
        deriving_failure(
          :cannot_derive_method,
          %{interface: interface, method: method, reason: reason},
          context,
          opts
        )

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
      |> then(fn opts ->
        if is_list(Map.get(context, :name_candidates)) do
          opts
          |> Keyword.put(:candidates, Map.get(context, :name_candidates))
          |> Keyword.put(:arity, Map.get(context, :name_arity))
        else
          opts
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
    do: inferred_hole_failure(name, %{}, opts)

  def from_error({kind, _detail} = error, opts)
      when kind in [
             :nonlinear_pattern,
             :duplicate_default_pattern,
             :impossible_default_pattern,
             :unreachable_after_default_pattern
           ],
      do: StaticAnalysis.from_error(error, opts)

  def from_error({kind} = error, opts) when kind in [:binary_match_needs_default, :map_match_needs_default],
    do: StaticAnalysis.from_error(error, opts)

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

  def from_error({:generated_hole_not_well_typed, term}, opts),
    do: generated_hole_invariant_failure(%{term: term}, %{}, opts)

  def from_error({:example_use_site_not_fully_consumed, _unused, _ast}, opts),
    do: macro_validation_failure(:example_use_site_not_fully_consumed, %{}, opts)

  def from_error({:closed_category_extension, categories}, opts),
    do: macro_module_failure(:closed_category_extension, %{categories: categories}, opts)

  def from_error({:ambiguous_macro_extension, keywords}, opts),
    do: macro_module_failure(:ambiguous_macro_extension, %{keywords: keywords}, opts)

  def from_error({kind, _detail}, opts) when kind in [:module_rule_not_fully_consumed, :not_a_module_rule],
    do: macro_module_failure(kind, %{}, opts)

  def from_error({:invalid_macro_rules, _detail}, opts),
    do: macro_family_failure(:invalid_macro_rules, opts)

  def from_error({kind, detail}, opts)
      when not is_map(detail) and
             kind in [
               :unknown_syntax_family,
               :duplicate_syntax_family,
               :duplicate_syntax_family_field,
               :syntax_family_cycle
             ],
      do: macro_family_failure({kind, detail}, opts)

  def from_error({:duplicate_unit, suffix}, opts),
    do: macro_unit_failure(:duplicate_unit, %{suffix: suffix}, opts)

  def from_error({kind, detail}, opts)
      when kind in [:invalid_unit, :unknown_unit],
      do: macro_unit_failure(kind, %{suffix: detail}, opts)

  def from_error({:invalid_unit_literal, value, suffix}, opts),
    do: macro_unit_failure(:invalid_unit_literal, %{value: value, suffix: suffix}, opts)

  def from_error({:invalid_check_name, name}, opts),
    do: macro_check_failure(:invalid_check_name, %{name: name}, opts)

  def from_error({:invalid_protocol_name, name}, opts),
    do: macro_protocol_failure(:invalid_protocol_name, %{name: name}, opts)

  def from_error({:protocol_role_count, count}, opts),
    do: macro_protocol_failure(:protocol_role_count, %{count: count}, opts)

  def from_error({kind, role}, opts)
      when kind in [:self_protocol_step, :unknown_choice_decider, :invalid_protocol_branches, :unprojectable_choice],
      do: macro_protocol_failure(kind, %{role: role}, opts)

  def from_error({:unknown_protocol_role, sender, receiver}, opts),
    do: macro_protocol_failure(:unknown_protocol_role, %{sender: sender, receiver: receiver}, opts)

  def from_error({:invalid_parse_name, name}, opts),
    do: macro_parse_failure(:invalid_parse_name, %{name: name}, opts)

  def from_error({:left_recursive_parse_production, names}, opts),
    do: macro_parse_failure(:left_recursive_parse_production, %{names: names}, opts)

  def from_error({:missing_raw_delimiter, delimiter}, opts),
    do: macro_raw_failure(:missing_raw_delimiter, %{delimiter: delimiter}, opts)

  def from_error({:invalid_raw_delimiter, delimiter}, opts),
    do: macro_raw_failure(:invalid_raw_delimiter, %{delimiter: delimiter}, opts)

  def from_error({kind, path}, opts)
      when kind in [
             :raw_syntax_in_expansion,
             :quoted_syntax_in_expansion,
             :malformed_expansion_syntax,
             :malformed_expansion_attribute,
             :malformed_expansion_map,
             :malformed_expansion_literal,
             :malformed_reflected_syntax,
             :malformed_reflected_attribute,
             :malformed_reflected_map,
             :malformed_reflected_literal
           ],
      do: macro_syntax_integrity_failure(kind, path, opts)

  def from_error({:invalid_syntax_node, _attrs, _kids}, opts),
    do: macro_syntax_decode_failure(:invalid_syntax_node, %{}, opts)

  def from_error({:invalid_syntax_node, _detail}, opts),
    do: macro_syntax_decode_failure(:invalid_syntax_node, %{}, opts)

  def from_error({:invalid_syntax_leaf, tag}, opts),
    do: macro_syntax_decode_failure(:invalid_syntax_leaf, %{tag: tag}, opts)

  def from_error({:invalid_syntax_failure, name}, opts),
    do: macro_syntax_decode_failure(:invalid_syntax_failure, %{name: name}, opts)

  def from_error({:unsupported_syntax_core, _term}, opts),
    do: macro_syntax_decode_failure(:unsupported_syntax_core, %{}, opts)

  def from_error({:invalid_syntax_attrs, _core}, opts),
    do: macro_syntax_decode_failure(:invalid_syntax_attrs, %{}, opts)

  def from_error({kind, _detail}, opts) when kind in [:invalid_macro_diagnostics, :invalid_macro_diagnostic],
    do: macro_diagnostic_schema_failure(kind, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_macro_segment,
             :unsupported_surface_filler,
             :missing_hole_filler,
             :invalid_repeated_hole_filler
           ],
      do: macro_fuzz_input_failure(kind, %{detail: detail}, opts)

  def from_error({kind, _detail}, opts)
      when kind in [
             :invalid_syntax_attr,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair
           ],
      do: macro_syntax_decode_failure(kind, %{}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_lift_module,
             :invalid_lift_module_name,
             :invalid_lift_callback,
             :invalid_module_name,
             :invalid_behaviour,
             :lifted_module_dependency_cycle,
             :duplicate_lifted_module
           ],
      do: lift_module_failure(kind, %{detail: detail}, opts)

  def from_error({:unknown_reducer_constructor, constructors}, opts),
    do: macro_reducer_failure(:unknown_reducer_constructor, %{constructors: constructors}, opts)

  def from_error({:incomplete_reducer, constructors}, opts),
    do: macro_reducer_failure(:incomplete_reducer, %{constructors: constructors}, opts)

  # Some trusted checking paths can return the bare verdict after their
  # declaration wrapper has been stripped. Keep that verdict contextual rather
  # than falling through to the unhelpful generic "Elaboration failed" title.
  def from_error(:branch_type, opts), do: TypeAdapter.from_error(:branch_type, opts)

  def from_error({kind, detail}, opts)
      when not is_map(detail) and
             kind in [
               :invalid_packet_name,
               :invalid_packet_endian,
               :unknown_packet_scalar,
               :missing_packet_endian,
               :forward_packet_length,
               :invalid_packet_crc_fields,
               :invalid_packet_field,
               :invalid_packet_field_name,
               :duplicate_packet_field,
               :invalid_driver_base,
               :invalid_driver_register,
               :duplicate_driver_register,
               :overlapping_driver_register,
               :unsupported_hole_type,
               :invalid_generated_syntax
             ],
      do: macro_validation_failure(kind, %{detail: detail}, opts)

  def from_error({kind, first, second}, opts)
      when kind in [:forward_packet_length, :invalid_packet_crc_fields, :reserved_syntax_field],
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
    do: macro_reducer_failure(:reducer_arity, %{constructor: constructor, actual: actual, expected: expected}, opts)

  def from_error({:primitive_missing_builtin, name}, opts),
    do: primitive_declaration_failure(:missing_builtin, %{name: name}, %{}, opts)

  def from_error({:unknown_primitive_tag, tag}, opts),
    do: primitive_declaration_failure(:unknown_builtin, %{tag: tag}, %{}, opts)

  def from_error({:primitive_floor_mismatch, name, declared, expected}, opts),
    do:
      primitive_declaration_failure(
        :floor_mismatch,
        %{name: name, declared: primitive_core_tag(declared), expected: primitive_core_tag(expected)},
        %{},
        opts
      )

  def from_error({:unsupported_declaration, shape}, opts),
    do: primitive_declaration_failure(:unsupported_declaration, %{shape: shape}, %{}, opts)

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

  def from_error({:applied_non_function, details} = error, opts) when is_map(details),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:effect_binder_erased, details}, opts) when is_map(details),
    do: erased_effect_binder_failure(details, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_driver_register,
             :duplicate_driver_register,
             :overlapping_driver_register
           ],
      do: macro_validation_failure(kind, %{}, opts)

  def from_error(kind, opts) when kind in [:no_compatible_macro_input, :normalization_fuel_exhausted],
    do: from_error({:computed_macro_error, [], kind}, opts)

  def from_error(kind, opts) when kind in [:invalid_macro_diagnostics, :invalid_macro_diagnostic],
    do: macro_diagnostic_schema_failure(kind, opts)

  def from_error(kind, opts)
      when kind in [:not_a_nat, :invalid_macro_fuzz_rule, :invalid_macro_fuzz_bindings],
      do: macro_fuzz_input_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_syntax_attr,
             :invalid_syntax_list,
             :invalid_syntax_string,
             :invalid_syntax_literal,
             :invalid_syntax_pair
           ],
      do: macro_syntax_decode_failure(kind, %{}, opts)

  def from_error(kind, opts) when kind in [:invalid_check_property, :duplicate_check_property],
    do: macro_check_failure(kind, %{}, opts)

  def from_error(:invalid_raw_tokens, opts), do: macro_raw_failure(:invalid_raw_tokens, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_lift_module_ast,
             :invalid_lift_callback,
             :invalid_lift_declaration,
             :invalid_lift_import,
             :invalid_lift_inheritance
           ],
      do: lift_module_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :module_rule_not_fully_consumed,
             :not_a_module_rule,
             :invalid_module_rule_set,
             :invalid_module_rule_bindings,
             :invalid_macro_extension_rules,
             :invalid_macro_extension_rule
           ],
      do: macro_module_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_macro_rules,
             :expander_without_accepts,
             :accepts_without_syntax_family,
             :accepts_without_expander,
             :multiple_accepts_declarations,
             :multiple_expands_declarations
           ],
      do: macro_family_failure(kind, opts)

  def from_error(kind, opts)
      when kind in [:invalid_parse_productions, :invalid_parse_production, :duplicate_parse_production],
      do: macro_parse_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_reducer_arms, :invalid_reducer_arm, :duplicate_reducer_constructor],
      do: macro_reducer_failure(kind, %{}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_protocol_roles,
             :invalid_protocol_role,
             :duplicate_protocol_role,
             :invalid_protocol_steps,
             :invalid_protocol_step,
             :invalid_protocol_message,
             :invalid_protocol_options,
             :invalid_protocol_choices,
             :invalid_protocol_choice
           ],
      do: macro_protocol_failure(kind, %{}, opts)

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

  def from_error({:no_instance, _interface, _head} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:ambiguous_instance_for_expected_type, interface, expected}, opts),
    do: contextual_type_failure(:ambiguous_instance, %{interface: interface, expected: expected}, opts)

  def from_error({:no_matching_overload, _name, _arguments} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:no_matching_overload, %{name: _name}} = error, opts),
    do: TypeAdapter.from_error(error, opts)

  def from_error({:label_mismatch, key, declared, written}, opts),
    do:
      contextual_type_failure(
        :label_mismatch,
        %{key: key, declared: declared, written: written},
        opts
      )

  def from_error({:ambiguous_overload, _name, _owners} = error, opts),
    do: TypeAdapter.from_error(error, opts)

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

  def from_error({:untyped_parameter, %{name: _name} = details}, opts),
    do: untyped_parameter_failure(details, opts)

  def from_error({:graded_let_needs_annotation, %{name: _name} = details}, opts),
    do: local_binding_annotation_failure(:graded, details, opts)

  def from_error({:let_needs_annotation, %{name: _name} = details}, opts),
    do: local_binding_annotation_failure(:ungraded, details, opts)

  def from_error({:typealias_not_a_type, %{name: _name, actual_type: _actual} = details}, opts),
    do: typealias_value_failure(details, opts)

  def from_error({:typealias_not_a_type, name, actual_type}, opts),
    do: typealias_value_failure(%{name: name, actual_type: actual_type}, opts)

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
             :unreachable_after_default_pattern,
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

  def from_error({kind, detail}, opts)
      when kind in [
             :unsupported_comprehension_pattern,
             :unsupported_binary_generator_pattern,
             :unsupported_binary_segment,
             :unsupported_binary_match_arm,
             :unsupported_map_match_arm,
             :unsupported_map_value_pattern,
             :unsupported_map_key_pattern,
             :unsupported_block_statement,
             :unsupported_block
           ],
      do: surface_structure_failure(kind, detail, opts)

  def from_error({kind, _name} = error, opts)
      when kind in [:unknown_global, :unbound_var, :unknown_family, :unknown_ctor, :foreign_ctor, :unknown_constructor],
      do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_global, _name, details} = error, opts) when is_map(details),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unknown_name, details} = error, opts) when is_map(details),
    do: NameAdapter.from_error(error, opts)

  def from_error({:unfilled_hole, details}, opts) when is_map(details) do
    opts = Keyword.put_new(opts, :span, Map.get(details, :span))
    primary = primary_label(opts, "replace this hole with an expression")

    secondary =
      case {Map.get(details, :annotation_span), primary} do
        {%Span{} = span, %Label{span: primary_span}} when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "this function's result type is declared here"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E014",
      key: :unfilled_hole,
      severity: :error,
      title: "Unfilled hole",
      body: Doc.paragraph("The definition `#{name_to_string(details.definition)}` still contains an unfinished hole."),
      primary: primary,
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Replace the hole with an expression that satisfies its surrounding type",
          applicability: :manual
        }
      ],
      payload: details
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
    from_error(
      {:extern_arity_mismatch, %{name: name, declared: declared, present: present}},
      opts
    )
  end

  def from_error({:call_arity_mismatch, %{name: name, expected: expected, actual: actual} = details}, opts)
      when is_integer(expected) and is_integer(actual) do
    difference = abs(expected - actual)

    {label, hint} =
      if actual < expected do
        {"add #{argument_count(difference)} to this call",
         "Supply the remaining #{argument_count(difference)}, or use this partial application where a function is expected."}
      else
        {"remove #{argument_count(difference)} from this call",
         "Remove the extra #{argument_count(difference)}, or call the returned function separately if that was intended."}
      end

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Function arity mismatch",
      body:
        Doc.paragraph(
          "`#{name_to_string(name)}` accepts #{argument_count(expected)}, but this call supplies #{argument_count(actual)}."
        ),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, :function)
    )
  end

  def from_error(
        {:extern_arity_mismatch, %{name: name, declared: declared, present: present} = details},
        opts
      )
      when is_integer(declared) and is_integer(present) do
    opts = Keyword.put_new(opts, :span, Map.get(details, :span))

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Arity mismatch",
      body:
        Doc.paragraph(
          "Extern `#{name_to_string(name)}` declares target arity #{declared}, but its present Cure arity is #{present}."
        ),
      primary:
        primary_label(
          opts,
          "change this target arity to #{present} so it matches the values present at runtime"
        ),
      suggestions: [
        %Suggestion{
          message: "Use target arity #{present}; erased parameters do not cross the FFI boundary.",
          applicability: :manual
        }
      ],
      payload:
        details
        |> Map.put(:name, name_to_string(name))
        |> Map.put(:kind, :extern)
    )
  end

  def from_error({:constructor_arity_mismatch, %{name: name} = details}, opts) do
    expected = Map.get(details, :expected)
    actual = Map.get(details, :actual)
    display_name = Map.get(details, :display_name) || name_to_string(name)

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Constructor arity mismatch",
      body:
        Doc.paragraph(
          "Constructor `#{display_name}` requires #{argument_count(expected)}, but this call supplies #{argument_count(actual)}."
        ),
      primary: primary_label(opts, constructor_arity_label(expected, actual)),
      payload:
        details
        |> Map.put(:kind, :constructor)
        |> Map.put(:constructor, display_name)
    )
  end

  def from_error({:constructor_arity_mismatch, name}, opts),
    do: from_error({:constructor_arity_mismatch, %{name: name}}, opts)

  def from_error(
        {:pattern_arity_mismatch, %{constructor: constructor, expected: expected, actual: actual} = details},
        opts
      ) do
    opts = Keyword.put(opts, :span, Map.get(details, :span))
    difference = abs(expected - actual)
    display_name = Map.get(details, :display_name) || name_to_string(constructor)

    {label, hint} =
      if actual < expected do
        {"add #{argument_count(difference)} to this pattern",
         "Bind the remaining constructor field#{if difference == 1, do: "", else: "s"}, or use `_` for fields you do not need."}
      else
        {"remove #{argument_count(difference)} from this pattern",
         "Remove the extra pattern field#{if difference == 1, do: "", else: "s"}; this constructor does not contain them."}
      end

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Pattern arity mismatch",
      body:
        Doc.paragraph(
          "Constructor `#{display_name}` has #{argument_count(expected)}, but this pattern matches #{argument_count(actual)}."
        ),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, :pattern)
    )
  end

  def from_error({:tuple_arity_mismatch, expected, actual}, opts)
      when is_integer(expected) and is_integer(actual) do
    difference = abs(expected - actual)

    {label, hint} =
      if actual < expected do
        {"add #{argument_count(difference)} to this tuple pattern",
         "Add #{argument_count(difference)} to match all #{expected} tuple elements; use `_` for values you do not need."}
      else
        {"remove #{argument_count(difference)} from this tuple pattern",
         "Remove #{argument_count(difference)}; this value has only #{argument_count(expected)}."}
      end

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "Tuple pattern has the wrong size",
      body:
        Doc.paragraph("This value has #{argument_count(expected)}, but the pattern contains #{argument_count(actual)}."),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: :tuple_pattern, expected: expected, actual: actual}
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
      payload: %{kind: :typed_pattern, annotation: surface_pattern_annotation(type_ast)}
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

  def from_error({:totality_required, _name} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:compile_time_totality, _name, _reason} = error, opts),
    do: StaticAnalysis.from_error(error, opts)

  def from_error({:pickup_no_else, details}, opts) when is_map(details) do
    clauses = pickup_spans(details.clauses)
    span = List.last(clauses) || details.pickup || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E076",
      key: :pickup_missing_else,
      severity: :error,
      title: "Pickup needs a fallback",
      body:
        Doc.paragraph(
          "A `pickup` must finish with a fallback branch so it has a result when no earlier condition is true."
        ),
      primary: pickup_label(span, :primary, "this is the final branch, but it is not a fallback"),
      suggestions: [
        %Suggestion{
          message: "Add `else -> ...` after this branch, or change the final condition to `true`",
          applicability: :manual
        }
      ],
      payload: Map.put(details, :repair_alternatives, [:append_else_branch, :use_trailing_true])
    )
  end

  def from_error({:pickup_else_not_last, details}, opts) when is_map(details) do
    clauses = pickup_spans(details.clauses)
    index = details.terminator_index
    else_span = details.else_clauses |> Enum.find_value(fn {idx, span} -> if idx == index, do: span end)
    primary_span = else_span || Enum.at(clauses, index) || Keyword.get(opts, :span)

    secondary =
      clauses
      |> Enum.drop(index + 1)
      |> Enum.map(&pickup_label(&1, :secondary, "this branch can never be reached after `else`"))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E077",
      key: :pickup_else_not_last,
      severity: :error,
      title: "Fallback branch is not last",
      body: Doc.paragraph("An `else` branch matches every remaining case, so no branch may follow it."),
      primary: pickup_label(primary_span, :primary, "this fallback matches everything that reaches it"),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: "Move the `else` branch after every conditional branch", applicability: :manual}
      ],
      payload: details
    )
  end

  def from_error({:pickup_multiple_else, details}, opts) when is_map(details) do
    else_spans = details.else_clauses |> Enum.map(&elem(&1, 1)) |> pickup_spans()
    primary_span = Enum.at(else_spans, 1) || List.first(else_spans) || Keyword.get(opts, :span)

    secondary =
      else_spans
      |> List.delete_at(1)
      |> Enum.map(&pickup_label(&1, :secondary, "another fallback branch is here"))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E078",
      key: :pickup_multiple_else,
      severity: :error,
      title: "Pickup has more than one fallback",
      body:
        Doc.paragraph(
          "Only one `else` branch is allowed because the first fallback already matches every remaining case."
        ),
      primary: pickup_label(primary_span, :primary, "this second fallback is redundant"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Keep one `else` branch and remove or give conditions to the others",
          applicability: :manual
        }
      ],
      payload: details
    )
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

  def from_error(%TypeProblem{} = problem, opts) do
    TypeAdapter.from_error(problem, opts)
  end

  def from_error(%SyntaxProblem{} = problem, opts) do
    span = problem.at || Keyword.get(opts, :span)
    code = Map.get(problem.context, :code, syntax_problem_code(problem.kind))

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

  def from_error({:conversion_failure, _actual, _expected} = error, opts),
    do: TypeAdapter.from_error(error, opts)

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

  def from_error({:expected_token, expected, actual_type, actual_value, line, column, %Span{} = span}, opts) do
    from_error(
      %SyntaxProblem{
        kind: missing_delimiter_kind(expected, actual_type),
        expected: expected,
        observed: if(is_nil(actual_value), do: actual_type, else: actual_value),
        at: Keyword.get(opts, :span, span),
        context: %{line: line, column: column, token_type: actual_type}
      },
      opts
    )
  end

  def from_error({:expected_literal_capture, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)
    article = article_for_kind(details.shape)

    Diagnostic.new(
      code: "E094",
      key: :macro_literal_capture,
      severity: :error,
      title: "Macro field needs a literal",
      body:
        Doc.paragraph(
          "This syntax-family field accepts #{article} `#{details.shape}` literal, not an expression of another shape."
        ),
      primary: pickup_label(span, :primary, "this is not #{article} `#{details.shape}` literal"),
      suggestions: [
        %Suggestion{
          message: "Replace this value with #{article} `#{details.shape}` literal",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:unknown_syntax_family_field, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :unknown_syntax_family_field,
      severity: :error,
      title: "Unknown syntax-family field",
      body: Doc.paragraph("`#{details.field}` is not a field of the `#{details.family}` syntax family."),
      primary: pickup_label(span, :primary, "this field is not declared by the family"),
      suggestions: syntax_family_field_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:missing_syntax_family_field, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :missing_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is missing",
      body: Doc.paragraph("The `#{details.family}` syntax family requires a `#{details.field}` section here."),
      primary: pickup_label(span, :primary, "add `#{details.field}` here"),
      suggestions: [
        %Suggestion{
          message: "Add a `#{details.field} ...` section to this family body",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:unknown_macro_obligation_capture, details}, opts) when is_map(details) do
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
      primary: pickup_label(span, :primary, "this capture is not declared by the rule"),
      suggestions: macro_capture_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:graded_let_requires_variable, details}, opts) when is_map(details) do
    pattern_span = Map.get(details, :pattern_span) || Keyword.get(opts, :span)
    grade_span = Map.get(details, :grade_span)

    secondary =
      case pickup_label(grade_span, :secondary, "this grade applies to the binding") do
        nil -> []
        label -> [label]
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
      primary: pickup_label(pattern_span, :primary, "this pattern is not a single variable binding"),
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
      primary: pickup_label(span, :primary, "this grade is not defined"),
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
      primary: pickup_label(span, :primary, "add the parameter type after this grade"),
      suggestions: [
        %Suggestion{message: "Write `#{details.name} :#{details.grade} TypeName`", applicability: :manual}
      ],
      payload: details
    )
  end

  def from_error({:unit_type_reserved, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case pickup_label(Map.get(details, :unit_span), :secondary, "this spelling denotes the built-in `Unit` type") do
        nil -> []
        label -> [label]
      end

    Diagnostic.new(
      code: "E092",
      key: :unit_type_reserved,
      severity: :error,
      title: "Unit syntax cannot define another type",
      body: Doc.paragraph("`()` has exactly one type, `Unit`, so it cannot define the new type `#{details.name}`."),
      primary: pickup_label(span, :primary, "this declaration must not reuse `Unit` syntax"),
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

  def from_error({:duplicate_syntax_family_field, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case pickup_label(Map.get(details, :first_span), :secondary, "the field was first supplied here") do
        nil -> []
        label -> [label]
      end

    Diagnostic.new(
      code: "E092",
      key: :duplicate_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is duplicated",
      body: Doc.paragraph("The `#{details.field}` field may be supplied only once in this family body."),
      primary: pickup_label(span, :primary, "this second `#{details.field}` field is redundant"),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: "Keep one `#{details.field}` section", applicability: :manual}
      ],
      payload: details
    )
  end

  def from_error({:non_associative, details}, opts) when is_map(details),
    do:
      from_error(
        %SyntaxProblem{
          kind: :non_associative,
          observed: details.next_operator,
          at: Map.get(details, :span) || Keyword.get(opts, :span),
          previous: Map.get(details, :operator_span),
          context: details
        },
        opts
      )

  def from_error({:ambiguous_precedence, details}, opts) when is_map(details),
    do:
      from_error(
        %SyntaxProblem{
          kind: :ambiguous_precedence,
          observed: details.operator,
          at: Map.get(details, :span) || Keyword.get(opts, :span),
          previous: Map.get(details, :operator_span),
          context: details
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

  def from_error({:unexpected_token, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.get(details, :kind, :unexpected_token),
        expected: Map.get(details, :expected),
        observed: details.observed,
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        context: details
      },
      opts
    )
  end

  def from_error({:missing_function_body, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :missing_function_body,
        expected: :expression,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        context: details
      },
      opts
    )
  end

  def from_error({:function_parameters_unparenthesized, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :function_parameters_unparenthesized,
        expected: :lparen,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        previous: Map.get(details, :name_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lambda_parameters_unparenthesized, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :lambda_parameters_unparenthesized,
        expected: :lparen,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :lambda_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lambda_arrow_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :lambda_arrow_missing,
        expected: :arrow,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :lambda_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:branch_arrow_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :branch_arrow_missing,
        expected: Map.get(details, :expected, :arrow),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:proof_command_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:macro_check_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:macro_rule_separator_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:syntax_family_definition_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        alternatives: Map.get(details, :alternatives, []),
        context: details
      },
      opts
    )
  end

  def from_error({:syntax_family_body_syntax, details}, opts) when is_map(details) do
    valid_fields = Map.get(details, :valid_fields, [])
    expected = Map.get(details, :expected) || List.first(valid_fields)

    alternatives =
      if Map.get(details, :kind) == :syntax_family_entry_invalid,
        do: Enum.drop(valid_fields, 1),
        else: []

    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: expected,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        previous: Map.get(details, :previous_span),
        alternatives: alternatives,
        context: details
      },
      opts
    )
  end

  def from_error({:macro_nested_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        alternatives: Map.get(details, :alternatives, []),
        context: details
      },
      opts
    )
  end

  def from_error({:refinement_type_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:sigma_type_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:declaration_separator_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:indexed_type_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:invalid_parameter_name, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :invalid_parameter_name,
        expected: :identifier,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        context: details
      },
      opts
    )
  end

  def from_error({:variadic_parameter_name_missing, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :variadic_parameter_name_missing,
        expected: :identifier,
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :marker_span),
        context: details
      },
      opts
    )
  end

  def from_error({:call_arguments_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:container_elements_syntax, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: Map.fetch!(details, :kind),
        expected: Map.get(details, :expected),
        observed: Map.get(details, :observed),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lambda_block_unterminated, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :unterminated_lambda,
        expected: Map.get(details, :expected, :end),
        observed: Map.get(details, :observed, :eof),
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :opener_span),
        previous: Map.get(details, :previous_span),
        context: details
      },
      opts
    )
  end

  def from_error({:lex_error, reason}, opts), do: from_error(lex_problem(reason, opts), opts)

  def from_error({:macro_use_mismatch, details}, opts) when is_map(details) do
    from_error(
      %SyntaxProblem{
        kind: :macro_use_mismatch,
        expected: details.expected,
        observed: details.got,
        at: Map.get(details, :span) || Keyword.get(opts, :span),
        opener: Map.get(details, :invocation_span),
        within: Map.get(details, :definition_span),
        alternatives: [],
        context: details
      },
      opts
    )
  end

  def from_error({:malformed_hole, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case pickup_label(Map.get(details, :opener_span), :secondary, "the macro hole starts here") do
        nil -> []
        label -> [label]
      end

    suggestions =
      case insertion_before(span) do
        %Span{} = insertion ->
          [
            %Suggestion{
              message: "Insert `>` to close the macro hole",
              applicability: :machine_applicable,
              edits: [%TextEdit{span: insertion, replacement: ">"}]
            }
          ]

        _ ->
          [%Suggestion{message: "Write the hole as `<name: Kind>`", applicability: :manual}]
      end

    Diagnostic.new(
      code: "E094",
      key: :malformed_macro_hole,
      severity: :error,
      title: "Macro hole is not closed",
      body:
        Doc.paragraph(
          "A typed macro hole has the form `<name: Kind>`. The closing `>` is missing before #{syntax_name(details.observed)}."
        ),
      primary: pickup_label(span, :primary, "expected `>` before this token"),
      secondary: secondary,
      suggestions: suggestions,
      payload: details
    )
  end

  def from_error({:edition_pragma_placement, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E094",
      key: :edition_pragma_placement,
      severity: :error,
      title: "Edition pragma is too late",
      body:
        Doc.paragraph(
          "`@edition(...)` selects how the entire file is read, so it must be the first non-comment item in the file."
        ),
      primary: pickup_label(span, :primary, "the edition cannot change after parsing has started"),
      suggestions: [
        %Suggestion{message: "Move this pragma above every declaration and decorator", applicability: :manual}
      ],
      payload: details
    )
  end

  def from_error({:edition_pragma_malformed, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E094",
      key: :edition_pragma_malformed,
      severity: :error,
      title: "Malformed edition pragma",
      body:
        Doc.paragraph(
          "An edition pragma must use the single-line form `@edition(\"YYYY\")` with exactly one four-digit string."
        ),
      primary: pickup_label(span, :primary, "this is not a valid edition argument"),
      suggestions: edition_replacement_suggestion(details),
      payload: details
    )
  end

  def from_error({:edition_pragma_unknown, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)
    observed = Map.get(details, :observed)
    known = Map.get(details, :known_editions, Cure.Edition.all())
    supported = Enum.map_join(known, ", ", &"`#{&1}`")

    Diagnostic.new(
      code: "E094",
      key: :edition_pragma_unknown,
      severity: :error,
      title: "Unknown edition",
      body:
        Doc.paragraph(
          "`#{name_to_string(observed)}` is not a supported Cure edition. This compiler supports #{supported}."
        ),
      primary: pickup_label(span, :primary, "this edition is not available"),
      suggestions: edition_replacement_suggestion(details),
      payload: details
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

  def from_error({:computed_macro_error, meta, {:host_exception, exception}}, opts)
      when is_list(meta) do
    keyword = Keyword.get(meta, :keyword, "computed")
    source_info = Metadata.source_info(meta)
    span = (source_info && source_info.whole) || Keyword.get(opts, :span)
    provenance = ((source_info && source_info.provenance) || []) ++ Keyword.get(opts, :provenance, [])
    exception_name = exception |> name_to_string() |> String.trim_leading("Elixir.")
    fingerprint = diagnostic_fingerprint({:computed_macro_host_exception, keyword, exception})

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Compiler failed while running a computed macro",
      body:
        Doc.paragraph(
          "The compiler raised `#{exception_name}` while evaluating the `#{keyword}` macro. This is a compiler defect, not a type or syntax error in the generated expansion. Diagnostic fingerprint: `#{fingerprint}`."
        ),
      primary: pickup_label(span, :primary, "this invocation reached the failing compiler path"),
      notes: ["Report this internal compiler failure with the diagnostic fingerprint."],
      suggestions: [
        %Suggestion{
          message: "Report fingerprint `#{fingerprint}` together with this source file",
          applicability: :manual
        }
      ],
      provenance: provenance,
      payload:
        %{stage: :computed_macro_expansion, macro: keyword, exception: exception_name, fingerprint: fingerprint}
        |> maybe_put_meta_location(meta)
    )
  end

  def from_error({:computed_macro_error, meta, reason}, opts) when is_list(meta) do
    keyword = Keyword.get(meta, :keyword, "computed")
    payload = %{keyword: keyword, reason: computed_macro_payload(reason)} |> maybe_put_meta_location(meta)
    source_info = Metadata.source_info(meta)
    span = (source_info && source_info.whole) || Keyword.get(opts, :span)
    provenance = ((source_info && source_info.provenance) || []) ++ Keyword.get(opts, :provenance, [])
    {title, message, primary_message, note} = computed_macro_content(keyword, reason)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: pickup_label(span, :primary, primary_message),
      notes: [note],
      suggestions: computed_macro_suggestions(reason),
      provenance: provenance,
      payload: payload
    )
  end

  def from_error({:invalid_macro_family, details}, opts) when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      details
      |> Map.get(:related_spans, [])
      |> Enum.map(&pickup_label(&1, :secondary, macro_family_related_label(details.reason)))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E092",
      key: :invalid_macro_family,
      severity: :error,
      title: macro_family_title(details.reason),
      body: Doc.paragraph(macro_family_body(details.reason)),
      primary: pickup_label(span, :primary, macro_family_primary_label(details.reason)),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: macro_family_hint(details.reason), applicability: :manual}
      ],
      payload: details
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
    Codegen.from_error({:beam_lint_error, errors, warnings}, opts)
  end

  def from_error({:beam_lint_error, errors}, opts) do
    Codegen.from_error({:beam_lint_error, errors}, opts)
  end

  def from_error({:final_core_violation, rejections}, opts) when is_list(rejections) do
    Codegen.from_error({:final_core_violation, rejections}, opts)
  end

  def from_error({:final_core_violation, name, rejections}, opts) when is_list(rejections) do
    Codegen.from_error({:final_core_violation, name, rejections}, opts)
  end

  def from_error({:expected_module, _ast} = error, opts), do: Codegen.from_error(error, opts)
  def from_error({:unsupported_container, _type} = error, opts), do: Codegen.from_error(error, opts)
  def from_error({:cannot_emit, _reason} = error, opts), do: Codegen.from_error(error, opts)

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
          notes: [
            "The generated module is an implementation detail; edit the authored `#{macro}` declaration instead."
          ],
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
             :unknown_macro_failure,
             :unsolved_metavariable_in_type,
             :lambda_expected_pi
           ],
      do: contextual_type_failure(kind, %{detail: detail}, opts)

  def from_error({kind, first, second}, opts)
      when kind in [:rewrite_no_match, :non_uniform_parameter],
      do: contextual_type_failure(kind, %{first: first, second: second}, opts)

  def from_error({:rewrite_no_match, first, second, goal}, opts),
    do: contextual_type_failure(:rewrite_no_match, %{first: first, second: second, goal: goal}, opts)

  def from_error({:bounded_lit_out_of_range, value, bound}, opts),
    do: bounded_literal_failure(value, bound, %{}, opts)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp unknown_record_failure(name, available_records, context, opts) do
    spelling = name_to_string(name)
    name_span = Map.get(context, :record_name_span) || Map.get(context, :span)

    candidates =
      Enum.map(available_records, fn candidate ->
        %{
          id: {:record, candidate},
          name: surface_declaration_name(candidate),
          namespace: :record,
          owner: record_owner(candidate),
          imported: true,
          visibility: :public,
          origin: :record_declaration
        }
      end)

    ranking_opts = Keyword.put(opts, :span, name_span)
    candidate_details = NameAdapter.rank_candidates(candidates, spelling, :record, ranking_opts)

    suggestions =
      case NameAdapter.candidate_suggestions(candidate_details, spelling, ranking_opts) do
        [] ->
          [
            %Suggestion{
              message: "Declare `rec #{spelling}` or import the module that defines it",
              applicability: :manual
            }
          ]

        ranked ->
          ranked
      end

    Diagnostic.new(
      code: "E021",
      key: :unknown_record,
      severity: :error,
      title: "Cannot find record `#{spelling}`",
      body: Doc.paragraph("No record named `#{spelling}` is available in this module or its imports."),
      primary:
        if(name_span,
          do: %Label{span: name_span, style: :primary, message: "this record name is not in scope"}
        ),
      suggestions: suggestions,
      payload: %{
        record: name,
        candidates: Enum.map(candidate_details, & &1.name),
        candidate_details: candidate_details,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp record_update_base_failure(details, context, opts) do
    record = Map.fetch!(details, :record)
    actual = Map.fetch!(details, :actual)
    record_surface = surface_declaration_name(record)
    actual_surface = if(is_atom(actual), do: surface_declaration_name(actual), else: surface_type(actual))
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
        if(base_span,
          do: %Label{span: base_span, style: :primary, message: "this value has type `#{actual_surface}`"},
          else: primary_label(opts, "use a `#{record_surface}` value here")
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Use a `#{record_surface}` value before `|`",
          applicability: :manual
        }
      ],
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

  defp extern_union_failure(kind, name, detail, context, opts) do
    name = surface_declaration_name(name)
    return_span = Map.get(context, :return_span) || Map.get(context, :span)
    extern_span = Map.get(context, :extern_span)
    member_ids = Map.get(context, :union_members, [])
    members = Enum.map(member_ids, &ffi_member_surface/1)

    {title, body, label, hint} =
      case kind do
        :nested ->
          union = if(members == [], do: "an anonymous union", else: Enum.join(members, " | "))

          {
            "Extern `#{name}` nests a union in its return type",
            "The return type contains `#{union}` inside another type. Erlang returns one raw value, and Cure can only identify and tag a union when that union is the outermost return type.",
            "this return type nests a union across the foreign boundary",
            "Return the union directly, or tag the nested value in the foreign function"
          }

        :indistinct ->
          {
            "Extern `#{name}` returns an indistinguishable union",
            ffi_indistinct_union_body(detail, members),
            "these union members have indistinguishable BEAM representations",
            "Return a tagged record or data type, or choose members with distinct BEAM shapes"
          }
      end

    secondary =
      case extern_span do
        %Span{} = span when span != return_span ->
          [%Label{span: span, style: :secondary, message: "this declaration crosses an Erlang boundary"}]

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
        if(return_span,
          do: %Label{span: return_span, style: :primary, message: label},
          else: primary_label(opts, label)
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: if(kind == :nested, do: :extern_returns_union, else: :extern_union_indistinct),
        name: name,
        union_member_ids: member_ids,
        union_members: members,
        conflict: ffi_union_conflict_payload(detail)
      }
    )
  end

  defp ffi_indistinct_union_body({:same_runtime_shape, [{left, right, runtime_class} | _]}, _members) do
    "`#{ffi_member_surface(left)}` and `#{ffi_member_surface(right)}` both arrive as BEAM #{runtime_shape_name(runtime_class)} values. Cure cannot tell which union alternative the foreign result belongs to."
  end

  defp ffi_indistinct_union_body({:same_erased_literal, [{left, right} | _]}, _members) do
    "`#{ffi_member_surface(left)}` and `#{ffi_member_surface(right)}` erase to the same BEAM value. Cure cannot tell which union alternative the foreign result belongs to."
  end

  defp ffi_indistinct_union_body({:unsupported_member_shape, unsupported}, _members) do
    "Cure has no single BEAM guard that can recognize #{Enum.map_join(unsupported, ", ", &"`#{ffi_member_surface(&1)}`")}. The raw foreign result therefore cannot be assigned to a union alternative safely."
  end

  defp ffi_indistinct_union_body(_reason, members) do
    union = if(members == [], do: "These union members", else: Enum.map_join(members, " and ", &"`#{&1}`"))
    "#{union} cannot be distinguished after crossing the foreign boundary."
  end

  defp ffi_union_conflict_payload({:same_runtime_shape, collisions}) do
    %{
      kind: :same_runtime_shape,
      pairs:
        Enum.map(collisions, fn {left, right, runtime_class} ->
          %{left: ffi_member_surface(left), right: ffi_member_surface(right), runtime_shape: runtime_class}
        end)
    }
  end

  defp ffi_union_conflict_payload({:same_erased_literal, collisions}) do
    %{
      kind: :same_erased_literal,
      pairs:
        Enum.map(collisions, fn {left, right} ->
          %{left: ffi_member_surface(left), right: ffi_member_surface(right)}
        end)
    }
  end

  defp ffi_union_conflict_payload({:unsupported_member_shape, members}),
    do: %{kind: :unsupported_member_shape, members: Enum.map(members, &ffi_member_surface/1)}

  defp ffi_union_conflict_payload(_detail), do: nil

  defp ffi_member_surface(member) do
    member = name_to_string(member)

    case String.split(member, "#", parts: 2) do
      [type, literal] when type in ["Int", "Nat", "Float", "String", "Atom", "Char", "Bool"] ->
        literal

      _ ->
        Regex.replace(~r/[A-Za-z_][A-Za-z0-9_.]*#([A-Za-z_][A-Za-z0-9_]*)/, member, "\\1")
    end
  end

  defp runtime_shape_name(:integer), do: "integer"
  defp runtime_shape_name(:float), do: "floating-point"
  defp runtime_shape_name(:binary), do: "binary"
  defp runtime_shape_name(:atom), do: "atom"
  defp runtime_shape_name(:boolean), do: "boolean"
  defp runtime_shape_name(:list), do: "list"
  defp runtime_shape_name(shape), do: name_to_string(shape)

  defp bounded_literal_failure(value, bound, context, opts) do
    literal_span = Map.get(context, :span) || Keyword.get(opts, :span)
    expectation_span = Map.get(context, :expectation_span)

    {interval, hint} =
      if is_integer(bound) and bound > 0 do
        {"from `0` through `#{bound - 1}`", "Use an integer from 0 through #{bound - 1}"}
      else
        {"in an empty interval because its bound is `#{bound}`", "Use a positive bound before constructing this value"}
      end

    secondary =
      case expectation_span do
        %Span{} = span when span != literal_span ->
          [%Label{span: span, style: :secondary, message: "this annotation requires `Bounded(#{bound})`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "#{value} is outside `Bounded(#{bound})`",
      body: Doc.paragraph("`Bounded(#{bound})` contains integer values #{interval}, but this literal is `#{value}`."),
      primary:
        if(literal_span,
          do: %Label{span: literal_span, style: :primary, message: "this value does not fit the declared bound"},
          else: primary_label(opts, "this value does not fit the declared bound")
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :bounded_lit_out_of_range,
        value: value,
        bound: bound,
        minimum: 0,
        maximum: if(is_integer(bound) and bound > 0, do: bound - 1, else: nil)
      }
    )
  end

  defp record_owner(name) do
    case name_to_string(name) |> String.split("#", parts: 2) do
      [owner, _name] -> owner
      [_name] -> nil
    end
  end

  defp dependent_record_projection_failure(record, field, context, opts) do
    record_name = surface_declaration_name(record)
    field = name_to_string(field)
    dependencies = Map.get(context, :dependent_fields, [])
    dependency_list = Enum.map_join(dependencies, ", ", &"`#{&1}`")
    primary_span = Map.get(context, :field_span) || Map.get(context, :span) || Keyword.get(opts, :span)
    receiver_span = Map.get(context, :receiver_span)
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
        sibling_dependency_label(
          receiver_span,
          primary_span,
          "this value has dependent record type `#{record_name}`"
        ),
        sibling_dependency_label(
          parameter_site_span(projected_site),
          primary_span,
          "`#{field}` is declared with a type that depends on #{dependency_phrase}"
        )
      ] ++
        Enum.flat_map(dependencies, fn dependency ->
          case dependent_sites |> Map.get(dependency) |> parameter_site_span() do
            %Span{} = span ->
              [
                sibling_dependency_label(
                  span,
                  primary_span,
                  "`#{dependency}` supplies part of `#{field}`'s type"
                )
              ]

            _ ->
              []
          end
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
        pickup_label(
          primary_span,
          :primary,
          "this projection separates `#{field}` from #{dependency_phrase}"
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

  defp projection_receiver_failure(record, context, opts) do
    field = context |> Map.get(:field) |> name_to_string()
    receiver_span = Map.get(context, :receiver_span) || Map.get(context, :span)
    field_span = Map.get(context, :field_span)
    actual_type = if(record, do: surface_declaration_name(record))

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
        if(receiver_span,
          do: %Label{span: receiver_span, style: :primary, message: receiver_message},
          else: primary_label(opts, receiver_message)
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Use a record value before `.#{field}`, or remove the projection",
          applicability: :manual
        }
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

  defp constructor_result_family_failure(family, context, opts) do
    expected = surface_declaration_name(Map.get(context, :expected_family, family))
    observed = surface_declaration_name(Map.get(context, :observed_family, :unknown))
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    parameter_count = Map.get(context, :parameter_count, 0)
    index_count = Map.get(context, :index_count, 0)
    primary_span = Map.get(context, :result_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        sibling_dependency_label(
          Map.get(context, :constructor_name_span),
          primary_span,
          "this constructor belongs to `#{expected}`"
        ),
        sibling_dependency_label(
          Map.get(context, :family_name_span),
          primary_span,
          "`#{expected}` is the family being declared"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{constructor}` returns `#{observed}` instead of `#{expected}`",
      body:
        Doc.paragraph(
          "Every constructor must produce a value of the type family that declares it. `#{constructor}` is declared under `#{expected}`, but the final type in its signature is `#{observed}`."
        ),
      primary:
        pickup_label(
          primary_span,
          :primary,
          "this result names `#{observed}`, not constructor family `#{expected}`"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: constructor_result_hint(expected, parameter_count, index_count),
          applicability: :manual
        }
      ],
      payload: %{
        kind: :result_type_not_family,
        family: expected,
        observed_family: observed,
        constructor: constructor,
        parameter_count: parameter_count,
        index_count: index_count
      }
    )
  end

  defp checked_constructor_result_failure(unsolved_name, context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    expected = constructor_result_surface_type(Map.get(context, :constructor_expected_type))
    actual = constructor_result_surface_type(Map.get(context, :constructor_actual_type))
    primary_span = Map.get(context, :application_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    argument_labels =
      context
      |> Map.get(:argument_spans, [])
      |> Enum.map(
        &sibling_dependency_label(
          &1,
          primary_span,
          "this argument did not provide enough information to recover from the incompatible result"
        )
      )

    secondary =
      [
        sibling_dependency_label(
          Map.get(context, :expectation_span),
          primary_span,
          "the surrounding annotation requires `#{expected}`"
        )
      ] ++ argument_labels

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "`#{constructor}` cannot produce the expected indexed type",
      body:
        Doc.stack([
          Doc.paragraph("This constructor produces `#{actual}`, but this position requires `#{expected}`."),
          Doc.paragraph(
            "Cure also could not infer the hidden arguments of `#{surface_declaration_name(unsolved_name)}` while checking the constructor fields. Supplying those arguments cannot make incompatible result indices agree."
          )
        ]),
      primary:
        pickup_label(
          primary_span,
          :primary,
          "this `#{constructor}` result cannot satisfy `#{expected}`"
        ),
      secondary: Enum.reject(secondary, &is_nil/1),
      suggestions: [
        %Suggestion{
          message: "Use a constructor whose result matches `#{expected}`, or change the surrounding result type",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :constructor_result_mismatch,
        semantic_reason: :unsolved_metavariables,
        unsolved_name: surface_declaration_name(unsolved_name),
        constructor: constructor,
        expected: expected,
        actual: actual,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp nested_constructor_implicit_failure(name, context, opts) do
    constructor = surface_declaration_name(name)
    owner = context |> Map.get(:checking, :constructor) |> surface_declaration_name()
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :expectation_span) do
        %Span{} = span when span != primary_span ->
          [
            pickup_label(
              span,
              :secondary,
              "the surrounding result still does not determine these indices"
            )
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "Cannot infer `#{constructor}` inside `#{owner}`",
      body:
        Doc.paragraph(
          "Argument #{argument_index + 1} of `#{owner}` uses `#{constructor}`, but its hidden type or index values are still unknown. The surrounding result and the other constructor fields do not determine them."
        ),
      primary:
        pickup_label(
          primary_span,
          :primary,
          "this nested constructor needs an expected indexed type"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message:
            "Use `#{constructor}` where its expected field type is known, or change the sibling arguments or result annotation so its indices are determined",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :nested_constructor_implicit,
        name: name,
        constructor: constructor,
        owner: Map.get(context, :checking),
        argument_index: argument_index,
        expectation_origin: :constructor_argument
      }
    )
  end

  defp constructor_result_surface_type({:data, family, parameters, indices}) do
    arguments = Enum.map(parameters ++ indices, &constructor_result_surface_type/1)
    name = surface_declaration_name(family)
    if arguments == [], do: name, else: "#{name}(#{Enum.join(arguments, ", ")})"
  end

  defp constructor_result_surface_type({:ctor, constructor, arguments}) do
    arguments = Enum.map(arguments, &constructor_result_surface_type/1)
    name = surface_declaration_name(constructor)
    if arguments == [], do: name, else: "#{name}(#{Enum.join(arguments, ", ")})"
  end

  defp constructor_result_surface_type({:global, name}), do: surface_declaration_name(name)
  defp constructor_result_surface_type({:meta, _id}), do: "?"
  defp constructor_result_surface_type(other), do: surface_type(other)

  defp typed_pattern_annotation_failure(context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    binder = name_to_string(Map.get(context, :binder, "field"))
    annotated = constructor_result_surface_type(Map.get(context, :annotated_type))
    field_type = constructor_result_surface_type(Map.get(context, :field_type))
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :annotation_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        sibling_dependency_label(
          Map.get(context, :binder_span) || Map.get(context, :typed_pattern_span),
          primary_span,
          "`#{binder}` is the field being annotated"
        ),
        sibling_dependency_label(
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
        pickup_label(
          primary_span,
          :primary,
          "this says `#{annotated}`, but the constructor field is `#{field_type}`"
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

  defp typed_pattern_arity_failure(context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    binder = name_to_string(Map.get(context, :binder, "field"))
    supplied = Map.get(context, :supplied_arity, 0)
    accepted = Map.get(context, :visible_arity, 0)
    argument_index = Map.get(context, :argument_index, accepted)
    primary_span = Map.get(context, :typed_pattern_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        sibling_dependency_label(
          Map.get(context, :constructor_name_span),
          primary_span,
          "`#{constructor}` accepts #{count_phrase(accepted, "visible field")}"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E003",
      key: :arity_mismatch,
      severity: :error,
      title: "`#{constructor}` pattern has #{count_phrase(supplied, "field")}, but the constructor has #{accepted}",
      body:
        Doc.paragraph(
          "`#{binder}` is field #{argument_index + 1} in this pattern, but `#{constructor}` exposes only #{count_phrase(accepted, "field")} to match. The pattern cannot bind a field that the constructor does not contain."
        ),
      primary:
        pickup_label(
          primary_span,
          :primary,
          "this extra field has no matching position in `#{constructor}`"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Remove the extra field, or use a constructor with #{count_phrase(supplied, "visible field")}",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :typed_pattern_arity,
        constructor: constructor,
        binder: binder,
        argument_index: argument_index,
        supplied_arity: supplied,
        visible_arity: accepted,
        checking: Map.get(context, :checking, :pattern)
      }
    )
  end

  defp positional_forced_pattern_failure(context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    argument_index = Map.get(context, :argument_index, 0)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :constructor_span) do
        %Span{} = span when span != primary_span ->
          [
            pickup_label(
              span,
              :secondary,
              "this constructor pattern supplies positional fields"
            )
          ]

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
        pickup_label(
          primary_span,
          :primary,
          "this forced check is in a positional field"
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

  defp forced_pattern_mismatch_failure(actual, expected, context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    implicit_name = name_to_string(Map.get(context, :implicit_name, "index"))
    actual_surface = Map.get(context, :written_surface) || constructor_result_surface_type(actual)
    expected_surface = Map.get(context, :expected_surface) || constructor_result_surface_type(expected)
    primary_span = Map.get(context, :forced_pattern_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        sibling_dependency_label(
          Map.get(context, :named_implicit_span),
          primary_span,
          "this check targets the hidden `#{implicit_name}` field"
        ),
        sibling_dependency_label(
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
        pickup_label(
          primary_span,
          :primary,
          "this forced value disagrees with the index fixed here"
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

  defp named_implicit_unforced_failure(name, context, opts) do
    constructor = surface_declaration_name(Map.get(context, :constructor, :constructor))
    implicit_name = name_to_string(name)
    primary_span = Map.get(context, :forced_pattern_span) || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        sibling_dependency_label(
          Map.get(context, :named_implicit_span),
          primary_span,
          "this pattern refers to hidden field `#{implicit_name}`"
        ),
        sibling_dependency_label(
          Map.get(context, :constructor_name_span),
          primary_span,
          "`#{constructor}` does not expose `#{implicit_name}` in its result index"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E011",
      key: :missing_implicit_argument,
      severity: :error,
      title: "`#{implicit_name}` is not fixed by matching `#{constructor}`",
      body:
        Doc.paragraph(
          "The result type of `#{constructor}` does not determine its hidden `#{implicit_name}` field. A dot pattern can only check a value already fixed by the scrutinee, so this field must be bound to a variable instead."
        ),
      primary:
        pickup_label(
          primary_span,
          :primary,
          "this dot expression has no forced value to check"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Replace the dot expression with a variable binding, for example `{#{implicit_name} = value}`",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :named_implicit_unforced,
        constructor: constructor,
        implicit_name: implicit_name,
        expectation_origin: :pattern
      }
    )
  end

  defp constructor_result_hint(family, 0, 0),
    do: "End this constructor signature with `#{family}`"

  defp constructor_result_hint(family, parameter_count, index_count) do
    positions =
      [
        if(parameter_count > 0, do: "#{parameter_count} #{plural(parameter_count, "parameter")}"),
        if(index_count > 0, do: "#{index_count} #{plural(index_count, "index")}")
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" and ")

    "End this constructor signature with `#{family}` applied to its #{positions}"
  end

  defp with_sibling_dependency_failure(details, context, opts) do
    dependent = name_to_string(Map.get(details, :dependent))
    dependency = name_to_string(Map.get(details, :dependency))
    reason = Map.get(details, :reason)
    dependent_site = parameter_site(context, dependent)
    dependency_site = parameter_site(context, dependency)
    expression_span = Map.get(context, :span) || Keyword.get(opts, :span)
    scrutinee_span = Map.get(context, :scrutinee_span)

    {body, primary_message, dependency_message, hint} =
      case reason do
        :sibling_references_sibling ->
          {
            "`#{dependent}` must be refined when this `with` chooses a constructor, but its type also depends on `#{dependency}`, which must be refined by the same match. Cure cannot currently generalize one refined sibling over another without changing their dependency order.",
            "the type of `#{dependent}` depends on another value refined by this `with`",
            "`#{dependency}` must also be refined by this match",
            "Nest a second match after refining `#{dependency}`, or change `#{dependent}` so its type does not depend on `#{dependency}`"
          }

        :kept_references_sibling ->
          {
            "`#{dependent}` is not itself refined by this `with`, but its type depends on `#{dependency}`, which is. Keeping `#{dependent}` while changing the type of `#{dependency}` would leave the context ill-formed.",
            "this parameter would keep a type tied to a refined sibling",
            "`#{dependency}` changes type across these branches",
            "Move `#{dependent}` inside the refined branch, or change its type so it does not depend on `#{dependency}`"
          }
      end

    primary_span = parameter_site_span(dependent_site) || expression_span

    secondary =
      [
        sibling_dependency_label(
          parameter_site_span(dependency_site),
          primary_span,
          dependency_message
        ),
        sibling_dependency_label(
          scrutinee_span,
          primary_span,
          "this is the value whose constructor would refine those sibling types"
        ),
        sibling_dependency_label(
          expression_span,
          primary_span,
          "this `with` requires the unsupported dependent refinement"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "With cannot refine dependent siblings in this order",
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: :with_sibling_dependency_unsupported,
        reason: reason,
        checking: Map.get(context, :checking),
        dependent: dependent,
        dependency: dependency
      }
    )
  end

  defp parameter_site(context, name) do
    context
    |> Map.get(:parameter_sites, [])
    |> Enum.find(&(name_to_string(Map.get(&1, :name)) == name))
  end

  defp parameter_site_span(%{type_span: %Span{} = span}), do: span
  defp parameter_site_span(%{span: %Span{} = span}), do: span
  defp parameter_site_span(_site), do: nil

  defp sibling_dependency_label(%Span{} = span, primary_span, message) when span != primary_span,
    do: pickup_label(span, :secondary, message)

  defp sibling_dependency_label(_span, _primary_span, _message), do: nil

  defp telescope_index_failure(index, arity, context, opts) do
    syntax = Map.get(context, :projection_syntax, :dot)

    primary_span =
      Map.get(context, :index_span) || Map.get(context, :field_span) || Map.get(context, :span) ||
        Keyword.get(opts, :span)

    receiver_span = Map.get(context, :receiver_span)
    expression_span = Map.get(context, :span)
    position_word = if arity == 1, do: "position", else: "positions"

    body =
      "This tuple has #{arity} #{position_word}, numbered from 1 through #{arity}, but this projection asks for position #{index}. Tuple projection is checked at compile time, so an out-of-range position can never produce a value."

    primary_message =
      case syntax do
        :element -> "index #{index} is outside this #{arity}-element tuple"
        _ -> "position .#{index} does not exist on this #{arity}-element tuple"
      end

    secondary =
      [
        sibling_dependency_label(
          receiver_span,
          primary_span,
          "this expression has a tuple type with #{arity} #{position_word}"
        ),
        sibling_dependency_label(
          expression_span,
          primary_span,
          "this complete projection cannot succeed"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Tuple position #{index} is out of range",
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Use a tuple position from 1 through #{arity}",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :telescope_index_out_of_bounds,
        index: index,
        arity: arity,
        syntax: syntax,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp pattern_only_syntax(kind, context, opts) do
    whole = Map.get(context, :span) || Keyword.get(opts, :span)
    opener = Map.get(context, :opener_span)
    name = Map.get(context, :name_span)
    body_span = Map.get(context, :body_span)

    {title, body, primary_span, primary_message, labels, hint} =
      case kind do
        :forced_pattern ->
          {
            "Forced value appears outside a pattern",
            "A leading dot marks a value that a constructor pattern must equal; it does not evaluate or access that value as an ordinary expression. This dot appears in expression position, where there is no surrounding pattern to force.",
            opener || whole,
            "this dot introduces pattern-only syntax",
            [{body_span, "this is the value the pattern would be forced to equal"}],
            "Remove the leading dot to use an ordinary expression, or move the forced value into a constructor pattern"
          }

        :named_implicit_pattern ->
          {
            "Named implicit appears outside a pattern",
            "`{name = pattern}` selects an implicit constructor field while matching a value. It cannot stand alone as an expression because no constructor pattern owns this implicit field.",
            whole,
            "this named implicit has no surrounding constructor pattern",
            [
              {name, "this names the constructor's implicit field"},
              {body_span, "this pattern would constrain that field"}
            ],
            "Move this named implicit inside a constructor pattern, or replace it with an ordinary expression"
          }
      end

    secondary =
      labels
      |> Enum.filter(fn {span, _message} -> match?(%Span{}, span) and span != primary_span end)
      |> Enum.map(fn {span, message} -> pickup_label(span, :secondary, message) end)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: kind,
        expression_category: Map.get(context, :expression_category),
        checking: Map.get(context, :checking)
      }
    )
  end

  defp rewrite_failure(kind, context, opts) do
    rewrite_span = Map.get(context, :span) || Keyword.get(opts, :span)
    proof_span = Map.get(context, :proof_span)
    body_span = Map.get(context, :body_span)

    {title, body, primary_span, primary_message, secondary, hint} =
      case kind do
        :rewrite_requires_expected_type ->
          {
            "Rewrite result needs an annotation",
            "A rewrite changes the type expected by its body, so Cure must know the surrounding result type before it can construct the equality motive. This rewrite appears where that type is still being inferred.",
            rewrite_span,
            "this rewrite has no expected result type",
            rewrite_context_labels(
              [
                {proof_span, "this proof determines what the body rewrites"},
                {body_span, "this body must be checked against the rewritten result"}
              ],
              rewrite_span
            ),
            "Add a result annotation to the enclosing declaration, or place this rewrite where an expected type is already known"
          }

        :rewrite_proof_not_equality ->
          {
            "Rewrite proof is not an equality",
            "The expression after `rewrite` must prove an `Equivalent(T, left, right)` proposition. This expression has another type, so it provides no endpoints that Cure can substitute in the body.",
            proof_span || rewrite_span,
            "this expression does not prove an equality",
            rewrite_context_labels(
              [{body_span, "this body would be checked after applying the equality"}],
              proof_span
            ),
            "Pass an `Equivalent` proof after `rewrite`, or remove `rewrite` if no equality is available"
          }

        :rewrite_no_match ->
          {
            "Rewrite does not change the goal",
            "The supplied equality is valid, but its left endpoint does not occur in the type required by this body. Applying it would leave the goal unchanged.",
            proof_span || rewrite_span,
            "this equality has no matching occurrence in the goal",
            rewrite_context_labels(
              [{body_span, "this body is checked against the unchanged goal"}],
              proof_span
            ),
            "Use an equality whose left endpoint occurs in the expected result, or remove this rewrite"
          }
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: kind,
        expression_category: Map.get(context, :expression_category, :rewrite_expr),
        checking: Map.get(context, :checking)
      }
    )
  end

  defp rewrite_context_labels(labels, primary_span) do
    labels
    |> Enum.filter(fn {span, _message} -> match?(%Span{}, span) and span != primary_span end)
    |> Enum.map(fn {span, message} -> pickup_label(span, :secondary, message) end)
  end

  defp local_binding_annotation_failure(kind, details, opts) do
    name = name_to_string(details.name)
    use_count = Map.get(details, :use_count)

    {title, body, primary_message, hint} =
      case {kind, use_count, Map.get(details, :reason)} do
        {:graded, _, _} ->
          grade = Map.get(details, :grade, :graded) |> name_to_string()

          {
            "Graded binding needs a type",
            "`#{name}` is declared `#{grade}`, but its initializer has no type Cure can synthesize without an expectation. Preserving the grade requires a real local binder, and Cure cannot construct that binder until its type is written.",
            "this grade cannot be preserved without a binding type",
            "Write the initializer's type after `:#{grade}`, before `=`"
          }

        {:ungraded, _, :shadowed_before_use} ->
          {
            "Shadowed binding needs a type",
            "Cure cannot synthesize a type for `#{name}`'s initializer. A later binder also uses the name `#{name}`, so substituting this initializer would cross that binding boundary and could capture the wrong value.",
            "this binding needs a type before it can cross a shadowing scope",
            "Add a type between `#{name}` and `=` so this value is bound once before the inner `#{name}`"
          }

        {:ungraded, 0, _} ->
          {
            "Unused binding needs a type",
            "Cure cannot synthesize a type for `#{name}`'s initializer. Because the binding is unused, substituting it would discard the initializer without checking or evaluating it.",
            "this unused binding cannot safely discard its initializer",
            "Add a type between `#{name}` and `=` so the initializer is checked exactly once"
          }

        {:ungraded, count, _} when is_integer(count) and count > 1 ->
          {
            "Repeated binding needs a type",
            "Cure cannot synthesize a type for `#{name}`'s initializer. Substituting the initializer at its #{count} uses would duplicate the expression instead of evaluating and binding it once.",
            "this binding would duplicate its initializer #{count} times",
            "Add a type between `#{name}` and `=` so the initializer is bound once"
          }

        _ ->
          {
            "Binding needs a type",
            "Cure cannot synthesize a type for `#{name}`'s initializer, so this local binding needs an explicit type.",
            "this binding needs an explicit type",
            "Add a type between `#{name}` and `=`"
          }
      end

    primary_span =
      case kind do
        :graded -> Map.get(details, :grade_span) || Map.get(details, :span)
        :ungraded -> Map.get(details, :name_span) || Map.get(details, :span)
      end || Keyword.get(opts, :span)

    secondary =
      [
        case Map.get(details, :initializer_span) do
          %Span{} = span when span != primary_span ->
            pickup_label(span, :secondary, "this initializer needs an expected type")

          _ ->
            nil
        end,
        case Map.get(details, :shadow_span) do
          %Span{} = span when span != primary_span ->
            pickup_label(span, :secondary, "this inner binder shadows `#{name}`")

          _ ->
            nil
        end
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{
        kind: if(kind == :graded, do: :graded_let_needs_annotation, else: :let_needs_annotation),
        name: name,
        grade: Map.get(details, :grade),
        use_count: use_count,
        reason: Map.get(details, :reason, :initializer_not_inferable)
      }
    )
  end

  defp typealias_value_failure(details, opts) do
    name = name_to_string(details.name)
    actual_surface = surface_type(details.actual_type)
    primary_span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(details, :name_span) do
        %Span{} = span when span != primary_span ->
          [pickup_label(span, :secondary, "this declaration promises a type alias")]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "`#{name}` aliases a value, not a type",
      body:
        Doc.paragraph(
          "The right side of a `typealias` must itself be a type, but this expression is a value whose type is `#{actual_surface}`. Type aliases give another name to a type; they cannot name one particular value."
        ),
      primary: pickup_label(primary_span, :primary, "this is a value of type `#{actual_surface}`"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "If `#{name}` should alias the value's type, write `typealias #{name} = #{actual_surface}`",
          applicability: :maybe_incorrect
        }
      ],
      payload: %{
        kind: :typealias_not_a_type,
        name: name,
        actual_surface: actual_surface,
        rhs_shape: Map.get(details, :rhs_shape, :expression)
      }
    )
  end

  defp untyped_parameter_failure(details, opts) do
    name = name_to_string(details.name)
    primary_span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "I need a type for `#{name}`",
      body:
        Doc.paragraph(
          "Cure cannot tell what values `#{name}` may receive from its name alone. Every ordinary function parameter needs a type annotation."
        ),
      primary: pickup_label(primary_span, :primary, "this parameter needs a type after its name"),
      suggestions: [
        %Suggestion{
          message:
            "Add a type annotation, such as `#{name}: Int`; write `{#{name}}` only for an implicit type parameter",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :untyped_parameter,
        name: name
      }
    )
  end

  defp argument_count(1), do: "1 argument"
  defp argument_count(count) when is_integer(count), do: "#{count} arguments"
  defp argument_count(_count), do: "a different number of arguments"

  defp constructor_arity_label(expected, actual)
       when is_integer(expected) and is_integer(actual) and actual < expected,
       do: "add #{argument_count(expected - actual)} to this constructor call"

  defp constructor_arity_label(expected, actual)
       when is_integer(expected) and is_integer(actual) and actual > expected,
       do: "remove #{argument_count(actual - expected)} from this constructor call"

  defp constructor_arity_label(_expected, _actual),
    do: "provide the arguments required by this constructor"

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
          span: Map.get(context, :expectation_span),
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
    frame_maps = Enum.filter(frames, &is_map/1)

    provenance =
      frame_maps
      |> Enum.map(fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword, "macro"),
          invocation: Map.get(frame, :invocation),
          definition: Map.get(frame, :definition),
          parent: Map.get(frame, :parent)
        }
      end)

    invocation_spans =
      frame_maps
      |> Enum.map(&Map.get(&1, :invocation))
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq()

    primary_span = List.last(invocation_spans) || Keyword.get(opts, :span)

    secondary =
      invocation_spans
      |> Enum.reject(&(&1 == primary_span))
      |> Enum.map(&pickup_label(&1, :secondary, "this earlier invocation is in the expansion chain"))

    suggestion =
      case kind do
        :cycle -> "Make recursive macro expansion consume input or terminate before invoking itself again"
        {:budget, _limit} -> "Reduce the generated expansion depth or split this macro into smaller steps"
      end

    chain =
      frames
      |> Enum.filter(&is_map/1)
      |> Enum.map(&Map.get(&1, :keyword))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: if(kind == :cycle, do: "Macro expansion cycle", else: "Macro expansion limit exceeded"),
      body: Doc.paragraph(message),
      primary:
        pickup_label(
          primary_span,
          :primary,
          if(kind == :cycle,
            do: "this invocation closes the expansion cycle",
            else: "the expansion limit is reached here"
          )
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: suggestion, applicability: :manual}],
      provenance: provenance ++ Keyword.get(opts, :provenance, []),
      payload: %{kind: kind, frames: frames, chain: chain}
    )
  end

  defp erased_effect_binder_failure(details, context, opts) do
    name = Map.get(context, :binder_name)
    type_span = Map.get(context, :span) || Keyword.get(opts, :span)
    binder_span = Map.get(context, :binder_span)
    opener = Map.get(context, :opener_span)
    closer = Map.get(context, :closer_span)

    binder_text = if name, do: " `#{name_to_string(name)}`", else: ""

    secondary =
      case binder_span do
        %Span{} = span when span != type_span ->
          [pickup_label(span, :secondary, "this parameter is declared inside erased implicit braces")]

        _ ->
          []
      end

    suggestions =
      case {opener, closer} do
        {%Span{} = open, %Span{} = close} ->
          [
            %Suggestion{
              message: "Make#{binder_text} a present parameter by removing the implicit braces",
              applicability: :machine_applicable,
              edits: [%TextEdit{span: open, replacement: ""}, %TextEdit{span: close, replacement: ""}]
            }
          ]

        _ ->
          [
            %Suggestion{
              message: "Make#{binder_text} a present parameter; an effect value cannot be erased",
              applicability: :manual
            }
          ]
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Effect parameter cannot be erased",
      body:
        Doc.paragraph(
          "The parameter#{binder_text} carries an `Effect` value, but implicit braces mark it for erasure. Removing that parameter at runtime could discard a computation the type says must remain available."
        ),
      primary: pickup_label(type_span, :primary, "this `Effect` type requires a runtime-present parameter"),
      secondary: secondary,
      suggestions: suggestions,
      payload: %{
        kind: :effect_binder_erased,
        definition: Map.get(details, :def),
        binder_index: Map.get(details, :binder),
        binder: name,
        expression_category: Map.get(context, :expression_category, :effect_binder)
      }
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

    spans = Map.get(details, :spans, [])
    {primary, secondary} = conflict_labels(spans, opts, kind, details)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: declaration_conflict_title(kind),
      body: Doc.paragraph(declaration_conflict_message(kind, name, conflict_message_detail(kind, details, detail))),
      primary: primary,
      secondary: secondary,
      suggestions: declaration_conflict_suggestions(kind, details),
      payload: Map.put(details, :kind, kind)
    )
  end

  defp conflict_labels([first, second | rest], _opts, kind, details) do
    primary = %Label{span: second, style: :primary, message: duplicate_primary_label(kind, details)}

    first_message =
      if Map.get(details, :operation),
        do: "this field was first supplied here",
        else: "the name was first declared here"

    secondary =
      [%Label{span: first, style: :secondary, message: first_message}] ++
        Enum.map(rest, &%Label{span: &1, style: :secondary, message: "another duplicate is here"})

    {primary, secondary}
  end

  defp conflict_labels(_spans, opts, kind, details),
    do: {primary_label(opts, duplicate_primary_label(kind, details)), []}

  defp declaration_conflict_title(:duplicate_parameter), do: "Duplicate parameter"
  defp declaration_conflict_title(:duplicate_field), do: "Duplicate field"
  defp declaration_conflict_title(:duplicate_index), do: "Duplicate index"
  defp declaration_conflict_title(:duplicate_type), do: "Duplicate type declaration"
  defp declaration_conflict_title(:duplicate_constructor), do: "Duplicate constructor"
  defp declaration_conflict_title(:sibling_module_collision), do: "Name repeated across sibling modules"
  defp declaration_conflict_title(_kind), do: "Declaration conflict"

  defp conflict_message_detail(:duplicate_field, %{operation: operation} = details, _detail)
       when operation in [:construction, :update],
       do: details

  defp conflict_message_detail(_kind, _details, detail), do: detail

  defp declaration_conflict_message(:duplicate_parameter, name, _detail),
    do:
      "The parameter `#{name}` is declared more than once. Rename or remove one occurrence so every parameter has a unique name."

  defp declaration_conflict_message(:duplicate_field, name, %{operation: operation, record: record}) do
    action = if(operation == :update, do: "updating", else: "constructing")

    "The field `#{name}` is supplied more than once while #{action} `#{surface_declaration_name(record)}`. A record value can provide each field only once."
  end

  defp declaration_conflict_message(:duplicate_field, name, _detail),
    do:
      "The field `#{name}` is declared more than once. Rename or remove one occurrence so every record field has a unique name."

  defp declaration_conflict_message(:duplicate_type, name, _detail),
    do:
      "The type `#{name}` is declared more than once in this module. Rename or remove one declaration so the type has a unique identity."

  defp declaration_conflict_message(:duplicate_constructor, name, _detail),
    do:
      "The constructor `#{name}` is declared more than once in this module. Rename or remove one declaration so pattern matching stays unambiguous."

  defp declaration_conflict_message(:sibling_module_collision, name, detail),
    do:
      "The name `#{name}` is declared#{detail}. Sibling modules in one source file currently share an elaboration namespace, so one declaration would overwrite the other. Rename one declaration or move the modules into separate source files."

  defp declaration_conflict_message(_kind, name, detail),
    do: "The declaration `#{name}` conflicts with another visible declaration#{detail}."

  defp duplicate_primary_label(:duplicate_field, %{operation: operation}) when operation in [:construction, :update],
    do: "this field is supplied again"

  defp duplicate_primary_label(:duplicate_parameter, _details), do: "this parameter repeats an earlier name"
  defp duplicate_primary_label(:duplicate_field, _details), do: "this field repeats an earlier name"
  defp duplicate_primary_label(:duplicate_index, _details), do: "this index repeats an earlier name"
  defp duplicate_primary_label(:duplicate_type, _details), do: "this type repeats an earlier declaration"
  defp duplicate_primary_label(:duplicate_constructor, _details), do: "this constructor repeats an earlier declaration"

  defp duplicate_primary_label(:sibling_module_collision, _details),
    do: "this name is already declared in another sibling module"

  defp duplicate_primary_label(_kind, _details), do: "rename this declaration or make its identity unique"

  defp declaration_conflict_suggestions(:duplicate_field, %{operation: operation, name: name})
       when operation in [:construction, :update] do
    [%Suggestion{message: "Remove one `#{name}` field", applicability: :manual}]
  end

  defp declaration_conflict_suggestions(_kind, _details), do: []

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

  defp method_signature_failure(details, opts) do
    interface = name_to_string(details.interface)
    method = name_to_string(details.method)
    expected_surface = if(details.expected, do: surface_type(details.expected), else: "the interface signature")
    actual_surface = if(details.actual, do: surface_type(details.actual), else: "an invalid method signature")
    primary_span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "Implementation method has the wrong signature",
      body:
        Doc.stack([
          Doc.paragraph(
            "`#{method}` in this `#{interface}` implementation has a different signature from the method declared by the interface. Every parameter and the result must agree after substituting the implementation type."
          ),
          TypeAdapter.comparison_doc(details.expected || expected_surface, details.actual || actual_surface)
        ]),
      primary: pickup_label(primary_span, :primary, "this implementation provides the incompatible signature"),
      suggestions: [
        %Suggestion{
          message: "Change `#{method}` to use the parameter and result types required by `#{interface}`",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :method_signature_mismatch,
        interface: interface,
        method: method,
        expected_surface: expected_surface,
        actual_surface: actual_surface
      }
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

  defp deriving_failure(kind, details, opts), do: deriving_failure(kind, details, %{}, opts)

  defp deriving_failure(kind, details, context, opts) do
    {title, message, label, hint} =
      case kind do
        :cannot_derive ->
          {"Cannot derive interface",
           "Cure cannot derive interface `#{name_to_string(details.interface)}` for this declaration.",
           "automatic derivation is unavailable for this interface",
           "Implement `#{name_to_string(details.interface)}` manually, or remove it from the deriving clause"}

        :deriving_needs_strings ->
          {"Deriving requires string support",
           "Interface `#{name_to_string(details.interface)}` can only be derived for a type with string-compatible members.",
           "this derived interface needs string-compatible members",
           "Use string-compatible members, or implement `#{name_to_string(details.interface)}` manually"}

        :deriving_needs_constraints ->
          {"Cannot derive `#{name_to_string(details.interface)}` for `#{name_to_string(details.type)}`",
           "A field of `#{name_to_string(details.type)}` uses one of the type's parameters directly. Deriving `#{name_to_string(details.interface)}` would need an interface dictionary for that parameter, which automatic derivation cannot thread yet.",
           "this derived interface needs a constraint on the type parameter",
           "Implement `#{name_to_string(details.interface)}` for `#{name_to_string(details.type)}` manually, or remove the parameter-typed field"}

        :cannot_derive_shape ->
          {"Cannot derive for this type shape",
           "Interface `#{name_to_string(details.interface)}` cannot be derived for `#{name_to_string(details.type)}` because its shape is unsupported.",
           "automatic derivation does not support this declaration shape",
           "Change the type shape, or implement `#{name_to_string(details.interface)}` manually"}

        :cannot_derive_method ->
          {"Cannot derive interface method",
           "Method `#{name_to_string(details.method)}` of `#{name_to_string(details.interface)}` cannot be generated for this type.",
           "this interface method cannot be generated", "Implement `#{name_to_string(details.method)}` explicitly"}
      end

    primary_span = Map.get(context, :deriving_span) || Map.get(context, :span) || Keyword.get(opts, :span)
    declaration_span = Map.get(context, :declaration_name_span) || Map.get(context, :declaration_span)
    declaration_name = Map.get(context, :checking) || Map.get(details, :type)

    secondary =
      case declaration_span do
        %Span{} = span when span != primary_span ->
          message =
            if declaration_name,
              do: "this declares `#{name_to_string(declaration_name)}`",
              else: "this is the declaration being derived"

          [%Label{span: span, style: :secondary, message: message}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary:
        if(primary_span,
          do: %Label{span: primary_span, style: :primary, message: label},
          else: primary_label(opts, label)
        ),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp operator_conflict(kind, details, opts) do
    {title, body, primary_message, secondary_message} =
      case kind do
        :precedence_cycle ->
          {"Cyclic operator precedence",
           "The precedence groups #{Enum.map_join(details.groups, ", ", &"`#{name_to_string(&1)}`")} form a cycle, so the compiler cannot decide which operators bind tighter. Remove or reverse one `higher_than`/`lower_than` relation to break the cycle.",
           "this precedence group participates in the cycle", "this precedence group also participates in the cycle"}

        :conflicting_operator_fixity ->
          {"Conflicting operator fixity",
           "The #{details.fixity} operator `#{details.operator}` is assigned to both `#{name_to_string(details.existing_group)}` and `#{name_to_string(details.new_group)}`. Keep one precedence group for this operator, or choose a different operator spelling.",
           "this declaration assigns `#{details.operator}` to `#{name_to_string(details.new_group)}`",
           "the conflicting assignment is here"}

        :conflicting_precedence_group ->
          {"Conflicting precedence group",
           "The precedence group `#{name_to_string(details.name)}` is declared with incompatible associativity or ordering rules. Give the declarations identical bodies, or rename one group.",
           "this declaration conflicts with the earlier group", "the incompatible group declaration is here"}
      end

    {primary, secondary} =
      operator_conflict_labels(Map.get(details, :spans, []), opts, primary_message, secondary_message)

    Diagnostic.new(
      code: "E106",
      key: :operator_declaration_conflict,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary,
      secondary: secondary,
      payload: Map.put(details, :kind, kind)
    )
  end

  defp operator_conflict_labels([first, second | rest], _opts, primary_message, secondary_message) do
    primary = %Label{span: second, style: :primary, message: primary_message}

    secondary =
      [%Label{span: first, style: :secondary, message: secondary_message}] ++
        Enum.map(rest, &%Label{span: &1, style: :secondary, message: secondary_message})

    {primary, secondary}
  end

  defp operator_conflict_labels([span], _opts, primary_message, _secondary_message),
    do: {%Label{span: span, style: :primary, message: primary_message}, []}

  defp operator_conflict_labels([], opts, primary_message, _secondary_message),
    do: {primary_label(opts, primary_message), []}

  defp inferred_hole_failure(name, context, opts) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    Diagnostic.new(
      code: "E014",
      key: :unfilled_hole,
      severity: :error,
      title: "Hole needs a type annotation",
      body:
        Doc.paragraph(
          "Cure cannot infer what this hole should contain because the surrounding definition has no declared result type."
        ),
      primary: primary_label(opts, "this hole has no expected type"),
      suggestions: [
        %Suggestion{
          message: "Declare the result type after `->`, then replace the hole with an expression of that type",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :inference_position,
        name: name,
        checking: Map.get(context, :checking, Keyword.get(opts, :checking))
      }
    )
  end

  defp primitive_declaration_failure(kind, details, context, opts) do
    name = Map.get(details, :name) || Map.get(context, :primitive)
    tag = Map.get(details, :tag) || Map.get(context, :builtin_tag)
    {title, body, primary_message, hint} = primitive_declaration_content(kind, name, tag, details)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case {kind, Map.get(context, :name_span)} do
        {kind, %Span{} = span} when kind in [:unknown_builtin, :floor_mismatch] and span != primary_span ->
          [
            %Label{
              span: span,
              style: :secondary,
              message: "this is the primitive declaration being validated"
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E120",
      key: :primitive_declaration,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary_label(Keyword.put(opts, :span, primary_span), primary_message),
      secondary: secondary,
      suggestions: primitive_declaration_suggestions(kind, details, context, hint),
      payload: %{
        kind: kind,
        name: name,
        tag: tag,
        declared: Map.get(details, :declared),
        expected: Map.get(details, :expected),
        shape: Map.get(details, :shape)
      }
    )
  end

  defp primitive_declaration_content(:missing_builtin, name, _tag, _details) do
    {
      "Primitive declaration needs a builtin tag",
      "`#{name_to_string(name)}` is declared as a primitive, but it has no `@builtin(...)` marker. The marker tells the compiler which runtime primitive representation this name denotes.",
      "add a `@builtin(...)` marker for this primitive",
      "Add one of `@builtin(:float)`, `@builtin(:binary)`, or `@builtin(:atom)` before this declaration"
    }
  end

  defp primitive_declaration_content(:unknown_builtin, _name, tag, _details) do
    {
      "`#{primitive_tag_spelling(tag)}` is not a primitive builtin",
      "The compiler has no primitive representation named `#{primitive_tag_spelling(tag)}`. Primitive declarations may currently use only `:float`, `:binary`, or `:atom`.",
      "this builtin tag is not recognized",
      "Use `:float`, `:binary`, or `:atom`, or declare an ordinary Cure type instead"
    }
  end

  defp primitive_declaration_content(:floor_mismatch, name, _tag, details) do
    declared = primitive_tag_spelling(Map.get(details, :declared))
    expected = primitive_tag_spelling(Map.get(details, :expected))

    {
      "`#{name_to_string(name)}` has the wrong primitive builtin",
      "`#{name_to_string(name)}` is part of the compiler's primitive floor and denotes `#{expected}`, but this declaration marks it as `#{declared}`. Those representations are not interchangeable.",
      "replace this tag with `#{expected}`",
      "Change the marker to `@builtin(#{expected})`"
    }
  end

  defp primitive_declaration_content(:unsupported_declaration, _name, _tag, details) do
    shape = details |> Map.get(:shape) |> name_to_string()

    {
      "Declaration form is not supported",
      "The elaborator received a `#{shape}` declaration form that this compiler does not support. If a macro generated this declaration, its expansion must use a supported declaration node.",
      "this declaration cannot be elaborated",
      "Rewrite this as a supported function, type, interface, implementation, or primitive declaration"
    }
  end

  defp primitive_declaration_suggestions(:floor_mismatch, details, context, hint) do
    expected = Map.get(details, :expected)

    case {Map.get(context, :builtin_argument_span), expected} do
      {%Span{} = span, tag} when is_atom(tag) ->
        [
          %Suggestion{
            message: hint,
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: primitive_tag_spelling(tag)}]
          }
        ]

      _ ->
        [%Suggestion{message: hint, applicability: :manual}]
    end
  end

  defp primitive_declaration_suggestions(_kind, _details, _context, hint),
    do: [%Suggestion{message: hint, applicability: :manual}]

  defp primitive_core_tag({:float_type}), do: :float
  defp primitive_core_tag({:binary_type}), do: :binary
  defp primitive_core_tag({:atom_type}), do: :atom
  defp primitive_core_tag(other) when is_atom(other), do: other
  defp primitive_core_tag(_other), do: :unknown

  defp primitive_tag_spelling(tag) when is_atom(tag), do: ":#{tag}"
  defp primitive_tag_spelling(tag), do: name_to_string(tag)

  defp overload_type_surface(type) when is_atom(type) or is_binary(type),
    do: name_to_string(Cure.Elab.Name.base(type) || type)

  defp overload_type_surface(type), do: surface_type(type)

  defp overload_declaration_signature(name, member) do
    parameters = Enum.map_join(Map.get(member, :parameters, []), ", ", &overload_type_surface/1)
    "#{name}(#{parameters})"
  end

  defp branch_pattern_span(%{pattern_span: %Span{} = span}), do: span
  defp branch_pattern_span(%{span: %Span{} = span}), do: span
  defp branch_pattern_span(_pattern), do: nil

  defp missing_branch_insertion_span(context) do
    case context |> Map.get(:branch_patterns, []) |> List.last() do
      %{span: %Span{} = span} ->
        %{span | start_byte: span.end_byte, start_line: span.end_line, start_column: span.end_column}

      _ ->
        nil
    end
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

  defp non_exhaustive_guard_failure(context, opts) do
    branches = Map.get(context, :branch_patterns, [])

    guard_labels =
      branches
      |> Enum.flat_map(fn
        %{guard_span: %Span{} = span} ->
          [pickup_label(span, :secondary, "this condition does not cover every remaining value")]

        _ ->
          []
      end)

    insertion = missing_branch_insertion_span(context)

    primary =
      case insertion do
        %Span{} = span -> pickup_label(span, :primary, "add an unguarded fallback branch here")
        _ -> pickup_label(Map.get(context, :span) || Keyword.get(opts, :span), :primary, "this match needs a fallback")
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Guarded branches leave a gap",
      body:
        Doc.paragraph(
          "Cure cannot prove that these guard conditions cover every value accepted by their patterns. If every condition is false, this match has no result."
        ),
      primary: primary,
      secondary: guard_labels,
      suggestions: [
        %Suggestion{
          message: "Add an unguarded `_ -> ...` branch, or make the final guards exact complements",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :non_exhaustive,
        checking: Map.get(context, :checking),
        guard_count: length(guard_labels)
      }
    )
  end

  defp shadowed_guard_binding_failure(details, context, opts) do
    name = name_to_string(details.name)
    site = Map.get(details, :site)
    outer_span = Map.get(details, :span)
    shadow_span = Map.get(details, :shadow_span)
    pattern_span = Map.get(details, :pattern_span)
    primary_span = shadow_span || outer_span || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      [
        case outer_span do
          %Span{} = span when span != primary_span ->
            pickup_label(span, :secondary, "this guard pattern binds `#{name}`")

          _ ->
            nil
        end,
        case pattern_span do
          %Span{} = span when span != primary_span and span != outer_span ->
            pickup_label(span, :secondary, "this is the guarded pattern")

          _ ->
            nil
        end
      ]
      |> Enum.reject(&is_nil/1)

    {title, body} =
      case site do
        :body ->
          {
            "Fallback branch shadows `#{name}`",
            "This fallback branch substitutes the matched value for `#{name}`, but a binder inside the branch uses the same name. That substitution could capture the inner value."
          }

        :constructor_branch ->
          {
            "Guarded constructor branch shadows `#{name}`",
            "This guarded constructor branch renames its pattern field `#{name}` during lowering, but a binder inside the branch uses the same name. That renaming could capture the inner value."
          }

        _ ->
          {
            "Guard branch shadows `#{name}`",
            "This guard branch substitutes the matched value for `#{name}`, but a binder inside the branch uses the same name. That substitution could capture the inner value."
          }
      end

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, "rename this inner binder so it does not shadow `#{name}`"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Give the nested binder a different name and update its branch expression",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :shadowed,
        name: name,
        site: site,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp refutable_guard_pattern_failure(details, context, opts) do
    shape = Map.get(details, :shape, :pattern)
    shape_name = guard_pattern_shape_name(shape)
    pattern_span = Map.get(details, :span)

    guard_span =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.find_value(fn branch ->
        if branch_pattern_span(branch) == pattern_span, do: Map.get(branch, :guard_span), else: nil
      end)

    secondary =
      case pickup_label(guard_span, :secondary, "this condition is attached to the refutable pattern") do
        nil -> []
        label -> [label]
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "#{String.capitalize(shape_name)} pattern cannot carry this guard",
      body:
        Doc.paragraph(
          "This #{shape_name} pattern can fail before its `when` condition is considered. The current guard chain only accepts variable, wildcard, or irrefutable tuple patterns."
        ),
      primary:
        pickup_label(
          pattern_span || Map.get(context, :span) || Keyword.get(opts, :span),
          :primary,
          "this refutable pattern cannot enter the guard chain"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Match this pattern first, then test the condition inside its branch and keep an explicit fallback",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :refutable_pattern,
        shape: shape,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp guard_pattern_shape_name(:literal), do: "literal"
  defp guard_pattern_shape_name(:tuple), do: "tuple"
  defp guard_pattern_shape_name(:function_call), do: "constructor"
  defp guard_pattern_shape_name(shape), do: shape |> name_to_string() |> String.replace("_", " ")

  defp complex_guard_scrutinee_failure(details, context, opts) do
    span =
      Map.get(details, :span) || Map.get(context, :scrutinee_span) || Map.get(context, :span) ||
        Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: "Guarded match needs a stable scrutinee",
      body:
        Doc.paragraph(
          "Guard conditions may inspect the matched value more than once. Bind this expression once before matching so its value is stable and any effects are not repeated."
        ),
      primary: pickup_label(span, :primary, "bind this expression before the guarded match"),
      suggestions: [
        %Suggestion{
          message: "Introduce a `let` binding for this expression, then match the new name",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_guard,
        reason: :complex_scrutinee,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp shadowed_sub_union_pattern_failure(details, context, opts) do
    name = name_to_string(details.name)
    reason = Map.get(details, :reason)
    outer_span = Map.get(details, :span)
    shadow_span = Map.get(details, :shadow_span)
    type_span = Map.get(details, :type_span)
    primary_span = shadow_span || outer_span || Map.get(context, :span) || Keyword.get(opts, :span)

    {body, type_message} =
      case reason do
        :shadowed_catchall ->
          {
            "This catch-all pattern binds the complete matched value as `#{name}`. A binder inside the branch uses the same name, so substituting the scrutinee could capture the inner value.",
            "this is the value bound by the catch-all"
          }

        :shadowed_literal_catchall ->
          {
            "After the preceding literal patterns fail, this catch-all binds the remaining value as `#{name}`. A binder inside the branch uses the same name, so substituting the scrutinee could capture the inner value.",
            "this is the value tested by the literal patterns"
          }

        :shadowed_default ->
          {
            "This fallback pattern binds every constructor not handled above as `#{name}`. A binder inside the fallback branch uses the same name, so reconstructing an omitted constructor could capture the inner value.",
            "this fallback receives the constructors not handled above"
          }

        :shadowed_tuple_arg ->
          {
            "This tuple pattern inside a constructor binds `#{name}` to one of the field's positions. A binder inside the branch uses the same name, so substituting the projection could capture the inner value.",
            "this constructor field is destructured as a tuple"
          }

        :shadowed_tuple ->
          {
            "This tuple pattern binds `#{name}` to one of the tuple's positions. A binder inside the branch uses the same name, so substituting the projection could capture the inner value.",
            "this tuple pattern is projected before its branch is checked"
          }

        :shadowed_nested ->
          {
            "This nested constructor pattern binds `#{name}`. A binder inside its branch uses the same name, so lowering the nested pattern could capture the inner value.",
            "this nested pattern is lowered before its branch is checked"
          }

        :shadowed_as ->
          {
            "The outer `#{name}` binds the complete value matched by this as-pattern. A nested binder uses the same name, so substituting the reconstructed value could capture the inner binding.",
            "this is the pattern reconstructed for the outer binding"
          }

        :shadowed_literal_member ->
          {
            "The outer `#{name}` stands for a literal union member. This nested pattern binds another value with the same name, so rewriting uses of the literal could capture the inner value.",
            "this branch names a literal union member"
          }

        _ ->
          {
            "The outer `#{name}` represents a narrowed union value. This nested pattern binds another value with the same name, so rewriting uses of the outer value could capture the inner one.",
            "this branch keeps the remaining union members"
          }
      end

    secondary =
      [
        case outer_span do
          %Span{} = span when span != primary_span ->
            pickup_label(span, :secondary, "this outer pattern binds `#{name}`")

          _ ->
            nil
        end,
        case type_span do
          %Span{} = span when span != primary_span and span != outer_span ->
            pickup_label(span, :secondary, type_message)

          _ ->
            nil
        end
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "Nested pattern shadows `#{name}`",
      body: Doc.paragraph(body),
      primary: pickup_label(primary_span, :primary, "rename this inner binder so it does not shadow `#{name}`"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Give the nested binder a different name and update its branch body",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_pattern,
        reason: reason,
        name: name,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp named_default_nonvariable_failure(details, context, opts) do
    name = name_to_string(details.name)
    pattern_span = Map.get(details, :span)
    scrutinee_span = Map.get(details, :type_span) || Map.get(context, :scrutinee_span)
    primary_span = pattern_span || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case pickup_label(
             scrutinee_span,
             :secondary,
             "this expression has no existing name for the catch-all to bind"
           ) do
        nil -> []
        label -> [label]
      end

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "Catch-all `#{name}` needs a stable value",
      body:
        Doc.paragraph(
          "This named catch-all must refer to the complete matched value, but the match scrutinizes an expression directly. Bind that expression once before matching so `#{name}` has an unambiguous value."
        ),
      primary: pickup_label(primary_span, :primary, "this catch-all needs the complete matched value"),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Bind the matched expression with `let`, then match the new name",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_pattern,
        reason: :named_default_nonvariable,
        name: name,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp with_default_pattern_failure(details, context, opts) do
    name = name_to_string(details.name)
    span = Map.get(details, :span) || Map.get(context, :span) || Keyword.get(opts, :span)

    constructor_labels =
      context
      |> Map.get(:with_arms, [])
      |> Enum.filter(&(Map.get(&1, :pattern_kind) == :constructor))
      |> Enum.map(&(Map.get(&1, :pattern_span) || Map.get(&1, :span)))
      |> Enum.map(&pickup_label(&1, :secondary, "this branch refines a constructor"))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "`with` needs constructor branches",
      body:
        Doc.paragraph(
          "The catch-all pattern `#{name}` does not identify a constructor, so it cannot refine the matched value or any dependent types. A `with` branch must restate one concrete constructor."
        ),
      primary: pickup_label(span, :primary, "replace this catch-all with a constructor pattern"),
      secondary: constructor_labels,
      suggestions: [
        %Suggestion{
          message: "Add the remaining constructor branches explicitly, or use `match` when no refinement is needed",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_pattern,
        reason: :default_in_with,
        name: name,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp unlowered_nested_constructor_failure(details, context, opts) do
    shape = details |> Map.get(:shape, :pattern) |> name_to_string()
    span = Map.get(details, :span) || Map.get(context, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E090",
      key: :unrecognized_pattern,
      severity: :error,
      title: "Nested constructor pattern could not be lowered",
      body:
        Doc.paragraph(
          "This nested `#{shape}` pattern reached a context that only accepts direct constructor binders. Split the nested test into a second match so each constructor is checked at its own level."
        ),
      primary: pickup_label(span, :primary, "move this nested pattern into a second match"),
      suggestions: [
        %Suggestion{
          message: "Bind this constructor field to a name, then match that name in the branch body",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :unsupported_pattern,
        reason: :unlowered_nested_constructor_argument,
        shape: shape,
        checking: Map.get(context, :checking)
      }
    )
  end

  defp rematch_pattern_failure(kind, details, context, opts) do
    primary_span = Map.get(context, :span) || Map.get(context, :rematch_arm_span) || Keyword.get(opts, :span)
    original_spans = Map.get(context, :original_pattern_spans, [])
    restated_spans = Map.get(context, :restated_pattern_spans, [])

    paired_original =
      restated_spans
      |> Enum.find_index(&(&1 == primary_span))
      |> then(fn
        nil -> Map.get(context, :original_patterns_span)
        index -> Enum.at(original_spans, index)
      end)

    {title, body, primary_message, hint} =
      rematch_pattern_content(kind, details, context)

    secondary =
      [
        rematch_label(paired_original, primary_span, "this is the corresponding original function pattern"),
        rematch_label(
          Map.get(context, :rematch_separator_span),
          primary_span,
          "patterns before this `|` restate the function's left-hand side"
        ),
        rematch_label(
          Map.get(context, :with_pattern_span),
          primary_span,
          "this pattern matches the value after `with`"
        )
      ]
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: body,
      primary: %Label{span: primary_span, style: :primary, message: primary_message},
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload:
        Map.merge(
          %{
            kind: kind,
            checking: Map.get(context, :checking),
            original_pattern_count: Map.get(context, :original_pattern_count),
            restated_pattern_count: Map.get(context, :restated_pattern_count)
          },
          details
        )
    )
  end

  defp rematch_context_enriched?(context),
    do: match?(%Span{}, Map.get(context, :span)) and is_list(Map.get(context, :restated_pattern_spans))

  defp rematch_pattern_content(:with_rematch_non_constructor_pattern, details, _context) do
    shape = Map.get(details, :details)

    {
      "Rematch pattern must describe a shape",
      Doc.stack([
        Doc.paragraph(
          "The left side of a `with` rematch restates the function's parameter patterns. It cannot evaluate an expression such as this `#{shape}` node."
        ),
        Doc.paragraph("Use variables and constructor patterns here; perform calculations in a guard or branch body.")
      ]),
      "this expression computes a value instead of matching a shape",
      "Replace this expression with a variable or constructor pattern, then move the calculation into the branch body"
    }
  end

  defp rematch_pattern_content(:with_rematch_ctor_mismatch, details, _context) do
    original = details |> Map.get(:original) |> name_to_string()
    restated = details |> Map.get(:restated) |> name_to_string()

    {
      "Rematch changes an existing constructor",
      Doc.paragraph(
        "The original function pattern uses `#{original}`, but this branch restates that same position with `#{restated}`. A rematch may refine variables, but it cannot replace an already-written constructor."
      ),
      "this restates `#{original}` as incompatible constructor `#{restated}`",
      "Keep `#{original}` at this position, or move this case into a separate function clause"
    }
  end

  defp rematch_pattern_content(:with_rematch_inconsistent_binding, details, _context) do
    name = details |> Map.get(:details) |> name_to_string()

    {
      "Rematch gives `#{name}` two different shapes",
      Doc.paragraph(
        "The original left-hand side binds `#{name}` more than once, but this rematch gives those occurrences different patterns. Every occurrence must describe the same value."
      ),
      "this occurrence disagrees with another restatement of `#{name}`",
      "Use the same variable or constructor pattern for every occurrence of `#{name}`"
    }
  end

  defp rematch_pattern_content(:with_rematch_arity_mismatch, details, context) do
    expected = Map.get(details, :expected, Map.get(context, :original_pattern_count))
    actual = Map.get(details, :actual, Map.get(context, :restated_pattern_count))

    {
      "Rematch has the wrong number of parent patterns",
      Doc.paragraph(
        "This function has #{expected} parent #{plural(expected, "pattern")}, but the branch restates #{actual}. The patterns before `|` must correspond position-for-position with the function's left-hand side."
      ),
      "these parent patterns do not match the function's arity",
      "Write exactly #{expected} #{plural(expected, "parent pattern")} before `|`"
    }
  end

  defp rematch_pattern_content(:with_rematch_unsupported_parent_pattern, details, _context) do
    shape = Map.get(details, :details)

    {
      "Original function pattern cannot be rematched",
      Doc.paragraph(
        "This function parameter uses a `#{shape}` pattern that the LHS-rematch algorithm cannot structurally refine."
      ),
      "this original pattern cannot participate in a `with` rematch",
      "Bind this parameter to a name first, then refine that name in the `with` branches"
    }
  end

  defp rematch_label(%Span{} = span, primary_span, message) when span != primary_span,
    do: %Label{span: span, style: :secondary, message: message}

  defp rematch_label(_span, _primary_span, _message), do: nil

  defp plural(1, singular), do: singular
  defp plural(_count, singular), do: singular <> "s"
  defp count_phrase(count, singular), do: "#{count} #{plural(count, singular)}"

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

        :bounded_family_unregistered ->
          {"Bounded type family is not registered",
           "This bounded type family is not available in the current checking environment.",
           "declare or import the bounded family before using it"}

        :absurd_in_reachable_position ->
          {"Absurd branch is reachable", "This branch claims an impossible value, but the scrutinee can reach it.",
           "refine the index or handle the reachable constructor"}

        :opaque_not_eliminable ->
          {"Opaque value cannot be eliminated",
           "This opaque value cannot be inspected in the current checking context.",
           "use its public interface instead of matching on its representation"}

        :case_scrutinee_not_data ->
          {"Case scrutinee is not data", "This case expression scrutinizes a value without data constructors.",
           "match a data-valued expression"}

        :not_total ->
          {"Definition is not total",
           "This definition does not cover every input or does not terminate by the required measure.",
           "add the missing cases or provide a decreasing recursive argument"}

        :not_a_function ->
          {"Application target is not callable", "This value is used as a function, but its type is not callable.",
           "apply a function or constructor value"}

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
          contextual_type_fallback(kind, opts)
      end

    TypeAdapter.contextual_failure(kind, details, opts, {title, message, label})
  end

  defp surface_structure_failure(kind, detail, opts) do
    {title, message, label, hint} = surface_structure_content(kind)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind, observed_shape: surface_ast_shape(detail)}
    )
  end

  defp surface_structure_content(:unsupported_comprehension_pattern) do
    {
      "List generator needs a variable pattern",
      "A list-comprehension generator can bind one variable in the dependent pipeline. This destructuring pattern cannot be translated without changing its matching behavior.",
      "bind one variable in this generator",
      "Bind one name here, then destructure it with `match` inside the comprehension body"
    }
  end

  defp surface_structure_content(:unsupported_binary_generator_pattern) do
    {
      "Binary generator needs one byte variable",
      "A binary-comprehension generator currently accepts one unsized, untyped byte variable. Sized segments, typed segments, and destructuring patterns do not have a supported runtime translation.",
      "use one plain byte variable here",
      "Write a generator such as `<<byte>> <- bytes`, then transform `byte` in the body"
    }
  end

  defp surface_structure_content(:unsupported_binary_segment) do
    {
      "Binary segment form is not supported",
      "Binary construction and matching currently support ordinary 8-bit byte expressions, plus a final variable `rest/binary` tail in patterns. This sized, typed, or otherwise structured segment cannot be lowered faithfully.",
      "this binary segment cannot be lowered",
      "Use plain byte segments, or move rich bit-syntax encoding and decoding behind an explicit binary helper"
    }
  end

  defp surface_structure_content(:unsupported_binary_match_arm) do
    {
      "Binary match arm has an unsupported pattern",
      "A binary match may use byte-segment patterns followed by a wildcard or variable fallback. This arm has a different pattern shape and cannot participate in the binary match translation.",
      "rewrite this binary match arm",
      "Use a `<<...>>` byte pattern here, or make this the final `_` fallback arm"
    }
  end

  defp surface_structure_content(:unsupported_map_match_arm) do
    {
      "Map match arm has an unsupported pattern",
      "A map match may use map patterns followed by a wildcard or variable fallback. This arm has a different pattern shape and cannot participate in the open-map match translation.",
      "rewrite this map match arm",
      "Use a `%{...}` map pattern here, or make this the final `_` fallback arm"
    }
  end

  defp surface_structure_content(:unsupported_map_value_pattern) do
    {
      "Map value pattern is not supported",
      "Map-pattern values may bind a variable, ignore the value with `_`, or compare it with a literal. Nested value patterns are not yet supported by the open-map translation.",
      "simplify this map value pattern",
      "Bind this value to one name, then inspect or match it inside the branch body"
    }
  end

  defp surface_structure_content(:unsupported_map_key_pattern) do
    {
      "Map pattern key must be an atom literal",
      "Map matching currently translates atom-literal keys into guarded lookups. A computed, variable, or non-atom key would require different matching semantics.",
      "use an atom literal as this map key",
      "Write a fixed atom key such as `status:`; use `get` explicitly for a dynamic key"
    }
  end

  defp surface_structure_content(:unsupported_block_statement) do
    {
      "Block statement must be a `let` binding",
      "Every non-final statement in an expression block must be a `let` binding. A plain assignment or expression before the final result has no sequencing meaning here.",
      "make this a `let` binding or the final expression",
      "Prefix this binding with `let`, or move the expression to the final line of the block"
    }
  end

  defp surface_structure_content(:unsupported_block) do
    {
      "Expression block has an unsupported shape",
      "An expression block must contain zero or more `let` bindings followed by exactly one final result expression.",
      "rewrite this expression block",
      "Keep `let` bindings first and finish the block with the value it should return"
    }
  end

  defp surface_ast_shape({tag, _meta, _children}) when is_atom(tag), do: tag
  defp surface_ast_shape([_ | _]), do: :sequence
  defp surface_ast_shape([]), do: :empty
  defp surface_ast_shape(value) when is_atom(value), do: value
  defp surface_ast_shape(_value), do: :unknown

  defp surface_detail_span({_tag, meta, children}) when is_list(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Span{} = span} -> span
      _ -> surface_child_span(children)
    end
  end

  defp surface_detail_span(meta) when is_list(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Span{} = span} -> span
      _ -> nil
    end
  end

  defp surface_detail_span(_detail), do: nil

  defp surface_child_span(children) when is_list(children) do
    spans = Enum.map(children, &surface_detail_span/1) |> Enum.reject(&is_nil/1)

    case spans do
      [] -> nil
      spans -> cover_surface_spans(spans)
    end
  end

  defp surface_child_span(_children), do: nil

  defp cover_surface_spans([%Span{} = first | rest]) do
    Enum.reduce(rest, first, fn %Span{} = span, %Span{} = covered ->
      if span.source_id == covered.source_id do
        %Span{
          covered
          | end_byte: max(covered.end_byte, span.end_byte),
            end_line: if(span.end_byte >= covered.end_byte, do: span.end_line, else: covered.end_line),
            end_column: if(span.end_byte >= covered.end_byte, do: span.end_column, else: covered.end_column)
        }
      else
        covered
      end
    end)
  end

  defp index_lowering_failure(kind, details, opts) do
    {title, message, label, hint} = index_lowering_content(kind, details)
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(Keyword.put(opts, :span, span), label),
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
      "An indexed constructor must return `#{name_to_string(family)}(...)`, but this result has a different type shape. The constructor's result is where its refined indices are declared.",
      "return the indexed family from this constructor",
      "Write this result as `#{name_to_string(family)}(...)` with one value for every declared index"
    }
  end

  defp index_lowering_content(:non_integer_index, details) do
    value = name_to_string(Map.get(details, :value))

    {
      "Dependent index must be a whole number",
      "`#{value}` is fractional, but a numeric dependent index denotes a natural number. Fractional values cannot identify a constructor position or bounded size.",
      "this index is not a whole number",
      "Use a non-negative integer index, or change the indexed family to carry a different numeric type"
    }
  end

  defp index_lowering_content(:unsupported_index_literal, details) do
    subtype = details |> Map.get(:subtype) |> name_to_string()

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
    operator = details |> Map.get(:operator) |> name_to_string()

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

  defp contextual_type_fallback(_kind, opts) do
    checking = Keyword.get(opts, :checking)
    origin = Keyword.get(opts, :expectation_origin)

    context_suffix =
      case checking do
        nil -> ""
        checking -> " while checking `#{name_to_string(checking)}`"
      end

    {title, message, label} =
      case origin do
        :annotation ->
          {"Expression does not match its annotation",
           "This expression does not satisfy the type required by its annotation#{context_suffix}.",
           "change the expression or its annotation"}

        :branch ->
          {"Branches have different types",
           "The branches of this match do not produce one compatible type#{context_suffix}.",
           "make the branches produce the same type"}

        :condition ->
          {"Condition has the wrong type",
           "This condition does not produce the type required by the conditional expression#{context_suffix}.",
           "make the condition produce `Bool`"}

        _ ->
          {"Cannot determine this expression's type",
           "Cure could not determine a valid type for this expression in its current checking context#{context_suffix}.",
           "add an annotation or revise this expression"}
      end

    {title, message, label}
  end

  defp ambiguous_member(method, interfaces, opts), do: ambiguous_member(method, interfaces, %{}, opts)

  defp ambiguous_member(method, interfaces, context, opts) do
    spelling = name_to_string(method)
    owners = Enum.map(interfaces, &name_to_string/1)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    declarations =
      context
      |> Map.get(:method_declarations, [])
      |> Enum.filter(&match?(%{span: %Span{}}, &1))

    secondary =
      declarations
      |> Enum.reject(&(&1.span == primary_span))
      |> Enum.map(fn declaration ->
        %Label{
          span: declaration.span,
          style: :secondary,
          message: "`#{spelling}` is also declared by `#{name_to_string(declaration.interface)}` here"
        }
      end)

    primary_owner =
      Enum.find_value(declarations, fn declaration ->
        if declaration.span == primary_span, do: name_to_string(declaration.interface)
      end)

    owner_list = Enum.map_join(owners, " and ", &"`#{&1}`")

    Diagnostic.new(
      code: "E089",
      key: :ambiguous_name,
      severity: :error,
      title: "Method `#{spelling}` is declared by multiple interfaces",
      body:
        Doc.paragraph(
          "Both #{owner_list} declare `#{spelling}`. Interface methods share one unqualified namespace, so Cure could not determine which declaration an unqualified `#{spelling}(...)` call should use."
        ),
      primary:
        if(primary_span,
          do: %Label{
            span: primary_span,
            style: :primary,
            message:
              if(primary_owner,
                do: "`#{primary_owner}` repeats the interface method `#{spelling}`",
                else: "this repeats the interface method `#{spelling}`"
              )
          },
          else: primary_label(opts, "rename this interface method")
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Rename `#{spelling}` in one interface so every interface method has a unique name",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :ambiguous_method,
        method: spelling,
        interfaces: owners,
        declarations:
          Enum.map(declarations, fn declaration ->
            %{interface: name_to_string(declaration.interface)}
          end)
      }
    )
  end

  defp inconsistent_interface_head(interface, context, opts) do
    interface = name_to_string(interface)
    parameter = name_to_string(Map.get(context, :head_parameter, "the head parameter"))
    uses = Map.get(context, :head_uses, [])
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    bare = Enum.find(uses, &(&1.kind == :bare and match?(%Span{}, &1.span)))
    applied = Enum.find(uses, &(&1.kind == :applied and match?(%Span{}, &1.span)))
    primary_span = (applied && applied.span) || primary_span

    secondary =
      case bare do
        %{span: %Span{} = span} when span != primary_span ->
          [
            %Label{
              span: span,
              style: :secondary,
              message: "`#{parameter}` is used as a complete type here"
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E105",
      key: :declaration_conflict,
      severity: :error,
      title: "`#{interface}` uses `#{parameter}` at two different kinds",
      body:
        Doc.paragraph(
          "The interface head `#{parameter}` is used both as a complete type and as a type constructor such as `#{parameter}(a)`. One interface parameter must have one consistent kind in every method signature."
        ),
      primary:
        if(primary_span,
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "`#{parameter}` is used as a type constructor here"
          },
          else: primary_label(opts, "use this interface parameter at one consistent kind")
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Use `#{parameter}` consistently as either a type or a type constructor",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :inconsistent_head_kind,
        interface: interface,
        head_parameter: parameter,
        uses:
          uses
          |> Enum.filter(&(&1.kind in [:bare, :applied]))
          |> Enum.uniq_by(& &1.kind)
          |> Enum.map(&%{kind: &1.kind, method: Map.get(&1, :method)})
      }
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

  defp expansion_proof_failure(details, context, opts) do
    keyword = Map.get(details, :keyword, Map.get(context, :keyword, "computed"))
    rule_kind = Map.get(context, :rule_kind)

    source =
      case rule_kind do
        :computed -> "computed expander"
        _ -> "expansion template"
      end

    payload = %{
      keyword: keyword,
      macro: Map.get(context, :macro),
      rule_kind: rule_kind,
      shrunk_hole: Map.get(details, :shrunk_hole)
    }

    payload =
      if Keyword.get(opts, :debug, false) do
        Map.merge(payload, %{
          generated_input: Map.get(details, :input),
          generated_bindings: Map.get(details, :generated_bindings),
          expansion: Map.get(details, :expansion),
          internal_reason: Map.get(details, :kernel_error) || Map.get(details, :reason)
        })
      else
        payload
      end

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "Macro rule can generate ill-typed code",
      body:
        Doc.paragraph("The `#{keyword}` rule has a generated counterexample that the dependent elaborator rejects."),
      primary: pickup_label(Map.get(context, :span), :primary, "this #{source} produces the invalid expansion"),
      suggestions: [
        %Suggestion{
          message: "Fix the `#{keyword}` rule so every accepted input produces well-typed Cure code",
          applicability: :manual
        }
      ],
      notes: ["The generated counterexample and internal elaboration reason are available in debug output."],
      provenance: Keyword.get(opts, :provenance, []),
      payload: payload
    )
  end

  defp generated_hole_invariant_failure(details, context, opts) do
    category = Map.get(details, :category, Map.get(context, :category, "unknown"))
    hole = Map.get(details, :hole, Map.get(context, :hole))
    fingerprint = diagnostic_fingerprint({:generated_hole_not_well_typed, category, hole, Map.get(details, :term)})

    payload = %{
      kind: :generated_hole_not_well_typed,
      macro: Map.get(context, :macro),
      category: category,
      hole: hole,
      fingerprint: fingerprint
    }

    payload =
      if Keyword.get(opts, :debug, false),
        do: Map.put(payload, :generated_term, Map.get(details, :term)),
        else: payload

    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      context
      |> Map.get(:hole_spans, [])
      |> Enum.map(&pickup_label(&1, :secondary, "this hole is affected by the same generator failure"))
      |> Enum.reject(&(&1.span == primary_span))

    Diagnostic.new(
      code: "E092",
      key: :macro_validation_failed,
      severity: :error,
      title: "Macro proof generator produced an invalid value",
      body:
        Doc.paragraph(
          "The compiler's `#{name_to_string(category)}` proof generator produced a value that failed its own type check. This is not an error in the macro declaration."
        ),
      primary: pickup_label(primary_span, :primary, "proof generation failed while checking this hole"),
      secondary: secondary,
      notes: ["Internal diagnostic fingerprint: #{fingerprint}."],
      suggestions: [
        %Suggestion{
          message: "Report this compiler defect with fingerprint `#{fingerprint}`",
          applicability: :manual
        }
      ],
      payload: payload
    )
  end

  defp macro_validation_failure(kind, details, opts), do: macro_validation_failure(kind, details, opts, %{})

  defp macro_packet_failure(kind, details, opts) do
    {title, message, label, hint} = macro_packet_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_packet_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_driver_failure(kind, details, opts) do
    {title, message, label, hint} = macro_driver_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_driver_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_board_failure(kind, details, opts) do
    {title, message, label, hint} = macro_board_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_board_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_unit_failure(kind, details, opts) do
    {title, message, label, hint} = macro_unit_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_unit_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_check_failure(kind, details, opts) do
    {title, message, label, hint} = macro_check_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_check_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_protocol_failure(kind, details, opts) do
    {title, message, label, hint} = macro_protocol_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_protocol_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_parse_failure(kind, details, opts) do
    {title, message, label, hint} = macro_parse_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_parse_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_reducer_failure(kind, details, opts) do
    {title, message, label, hint} = macro_reducer_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_reducer_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_raw_failure(kind, details, opts) do
    {title, message, label, hint} = macro_raw_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_raw_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_syntax_integrity_failure(kind, path, opts) do
    {title, message, label, hint} = macro_syntax_integrity_content(kind, path)

    Diagnostic.new(
      code: "E092",
      key: :macro_syntax_integrity,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind, path: path}
    )
  end

  defp macro_syntax_decode_failure(kind, details, opts) do
    {title, message, label, hint} = macro_syntax_decode_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_syntax_decode,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_diagnostic_schema_failure(kind, opts) do
    {title, message, label, hint} = macro_diagnostic_schema_content(kind)

    Diagnostic.new(
      code: "E092",
      key: :macro_diagnostic_schema,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{kind: kind}
    )
  end

  defp macro_fuzz_input_failure(kind, details, opts) do
    {title, message, label, hint} = macro_fuzz_input_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_fuzz_input,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: macro_fuzz_payload(kind, details)
    )
  end

  defp macro_fuzz_input_content(:invalid_macro_fuzz_rule, _details),
    do:
      {"Macro proof rule is malformed",
       "Proof-input assembly needs a parsed macro rule with a textual keyword and segment list.",
       "rewrite this macro rule", "Provide a parsed syntax or computed rule"}

  defp macro_fuzz_input_content(:invalid_macro_fuzz_bindings, _details),
    do:
      {"Macro proof bindings are malformed",
       "Generated hole bindings must map each textual hole name to its sampled value.",
       "rewrite these generated bindings", "Provide a map from hole names to generated values"}

  defp macro_fuzz_input_content(:invalid_macro_segment, _details),
    do:
      {"Macro rule contains an unsupported segment",
       "Proof-input assembly encountered a rule segment that is not a literal, hole, repetition, optional group, raw hole, or declaration body.",
       "replace this macro segment", "Use one of the supported macro rule segment forms"}

  defp macro_fuzz_input_content(:missing_hole_filler, %{detail: name}),
    do:
      {"Generated macro input is missing a hole",
       "The proof input has no generated value for the `#{name_to_string(name)}` hole required by this rule.",
       "supply this generated hole", "Add a generated value for `#{name_to_string(name)}`"}

  defp macro_fuzz_input_content(:invalid_repeated_hole_filler, %{detail: name}),
    do:
      {"Repeated macro hole needs a list",
       "The `#{name_to_string(name)}` hole is repeated by the rule, but its generated filler is not a list of values.",
       "replace this repeated-hole filler", "Provide a list of generated values for `#{name_to_string(name)}`"}

  defp macro_fuzz_input_content(:unsupported_surface_filler, _details),
    do:
      {"Generated hole has no surface spelling",
       "The proof generator produced a Core value that cannot be written as authored Cure macro input.",
       "use a surface-encodable generator",
       "Generate a literal, nullary constructor, raw text, natural, boolean, or supported type value"}

  defp macro_fuzz_input_content(:not_a_nat, _details),
    do:
      {"Generated natural number is malformed",
       "A sampled natural must be built only from `Z` and unary `S` constructors.",
       "replace this natural-number sample", "Generate `Z` or `S(previous_nat)`"}

  defp macro_fuzz_payload(kind, %{detail: detail})
       when kind in [:missing_hole_filler, :invalid_repeated_hole_filler],
       do: %{kind: kind, hole: name_to_string(detail)}

  defp macro_fuzz_payload(kind, _details), do: %{kind: kind}

  defp macro_diagnostic_schema_content(:invalid_macro_diagnostics),
    do:
      {"Macro rejection list is malformed",
       "A rejected macro result must contain one author diagnostic or a proper list of author diagnostics.",
       "rebuild this macro rejection", "Return `Rejected([Failure(name, arguments), ...])`"}

  defp macro_diagnostic_schema_content(:invalid_macro_diagnostic),
    do:
      {"Macro author diagnostic is malformed",
       "A macro author diagnostic must be a reflected `Failure` value with an atom name and syntax arguments.",
       "rebuild this author diagnostic", "Return `Failure(name, arguments)` inside `Rejected`"}

  defp macro_syntax_decode_content(:invalid_syntax_node, _details),
    do:
      {"Generated syntax node is malformed",
       "A reflected `Node` must contain an atom tag, an attribute list, and a list of syntax children.",
       "rebuild this syntax node", "Construct `Node(tag, attributes, children)` with valid values"}

  defp macro_syntax_decode_content(:invalid_syntax_leaf, %{tag: tag}),
    do:
      {"Generated syntax leaf is malformed",
       "The `#{name_to_string(tag)}` reflected `Leaf` does not contain a valid attribute list and syntax literal.",
       "rebuild this syntax leaf", "Construct `Leaf(tag, attributes, literal)` with valid values"}

  defp macro_syntax_decode_content(:invalid_syntax_failure, %{name: name}),
    do:
      {"Macro failure value is malformed",
       "The `#{name_to_string(name)}` failure does not contain a valid list of reflected syntax arguments.",
       "rebuild this macro failure", "Construct `Failure(name, arguments)` with valid syntax arguments"}

  defp macro_syntax_decode_content(:unsupported_syntax_core, _details),
    do:
      {"Macro returned a non-syntax value",
       "The computed macro returned a Core value that is not a `Std.Syntax` constructor.", "return a syntax value here",
       "Return `Node`, `Leaf`, `Raw`, `Quoted`, or `Failure` from the macro"}

  defp macro_syntax_decode_content(:invalid_syntax_attrs, _details),
    do:
      {"Generated syntax attributes are malformed",
       "Syntax attributes must be a `Std.List` of atom-keyed `KV` entries.", "rebuild this attribute list",
       "Use `KV(atom_key, syntax_literal)` for every attribute"}

  defp macro_syntax_decode_content(:invalid_syntax_attr, _details),
    do:
      {"Generated syntax attribute is malformed",
       "A syntax attribute must be an atom-keyed `KV` entry containing a valid syntax literal.",
       "rebuild this syntax attribute", "Use `KV(atom_key, syntax_literal)`"}

  defp macro_syntax_decode_content(:invalid_syntax_list, _details),
    do:
      {"Generated syntax list is malformed",
       "A reflected syntax list must use the `Std.List` `Nil` and `Cons` constructors.", "rebuild this syntax list",
       "Construct a proper `Std.List` value"}

  defp macro_syntax_decode_content(:invalid_syntax_string, _details),
    do:
      {"Generated syntax string is malformed",
       "A reflected syntax string must contain a proper list of bounded character literals.",
       "rebuild this syntax string", "Construct `SStr` from valid character values"}

  defp macro_syntax_decode_content(:invalid_syntax_literal, _details),
    do:
      {"Generated syntax literal is malformed",
       "This value is not one of the supported `Std.Syntax` literal constructors.", "replace this syntax literal",
       "Use `SInt`, `SFloat`, `SStr`, `SBool`, `SAtom`, `SList`, `SSyntax`, `SMap`, or `SOpaque`"}

  defp macro_syntax_decode_content(:invalid_syntax_pair, _details),
    do:
      {"Generated syntax-map pair is malformed",
       "Every entry in an `SMap` must be an `SPair` containing two valid syntax literals.",
       "rebuild this syntax-map pair", "Use `SPair(key, value)` inside `SMap`"}

  defp macro_syntax_integrity_content(:raw_syntax_in_expansion, path),
    do:
      {"Macro expansion contains raw syntax",
       "The generated expansion contains reflection-only raw syntax at #{syntax_path_phrase(path)}.",
       "return executable syntax here", "Build structured `Syntax`; keep `Raw` values inside reflected metadata"}

  defp macro_syntax_integrity_content(:quoted_syntax_in_expansion, path),
    do:
      {"Macro expansion contains quoted syntax",
       "The generated expansion still contains quoted syntax at #{syntax_path_phrase(path)}.",
       "unquote this generated syntax", "Splice or otherwise unquote the value before returning the expansion"}

  defp macro_syntax_integrity_content(:malformed_expansion_syntax, path),
    do:
      {"Macro expansion syntax is malformed",
       "The generated expansion does not contain a valid `Node`, `Leaf`, or accepted failure value at #{syntax_path_phrase(path)}.",
       "rebuild this generated syntax", "Return a well-formed structured `Syntax` value"}

  defp macro_syntax_integrity_content(:malformed_expansion_attribute, path),
    do:
      {"Macro expansion attribute is malformed",
       "A generated syntax attribute is not an atom-keyed literal pair at #{syntax_path_phrase(path)}.",
       "rebuild this syntax attribute", "Use an atom key and a valid syntax literal value"}

  defp macro_syntax_integrity_content(:malformed_expansion_map, path),
    do:
      {"Macro expansion map literal is malformed",
       "A generated syntax-map entry is not a key-value pair at #{syntax_path_phrase(path)}.",
       "rebuild this syntax map", "Provide valid syntax-literal key-value pairs"}

  defp macro_syntax_integrity_content(:malformed_expansion_literal, path),
    do:
      {"Macro expansion literal is malformed",
       "A generated syntax literal has the wrong shape or host value at #{syntax_path_phrase(path)}.",
       "replace this syntax literal",
       "Use a valid integer, float, string, boolean, atom, list, map, syntax, or opaque literal"}

  defp macro_syntax_integrity_content(:malformed_reflected_syntax, path),
    do:
      {"Reflected syntax value is malformed",
       "Syntax stored inside generated metadata has an invalid node shape at #{syntax_path_phrase(path)}.",
       "rebuild this reflected syntax", "Store a well-formed reflected `Syntax` value"}

  defp macro_syntax_integrity_content(:malformed_reflected_attribute, path),
    do:
      {"Reflected syntax attribute is malformed",
       "An attribute inside reflected syntax is not an atom-keyed literal pair at #{syntax_path_phrase(path)}.",
       "rebuild this reflected attribute", "Use an atom key and a valid reflected literal value"}

  defp macro_syntax_integrity_content(:malformed_reflected_map, path),
    do:
      {"Reflected syntax map is malformed",
       "A map stored inside reflected syntax contains an entry that is not a key-value pair at #{syntax_path_phrase(path)}.",
       "rebuild this reflected map", "Provide valid reflected-literal key-value pairs"}

  defp macro_syntax_integrity_content(:malformed_reflected_literal, path),
    do:
      {"Reflected syntax literal is malformed",
       "A literal stored inside reflected syntax has the wrong shape or host value at #{syntax_path_phrase(path)}.",
       "replace this reflected literal", "Use a valid reflected syntax literal"}

  defp macro_syntax_integrity_content(kind, path),
    do:
      {"Macro syntax value is invalid",
       "Generated syntax failed the `#{name_to_string(kind)}` integrity check at #{syntax_path_phrase(path)}.",
       "rebuild this generated syntax", "Return a well-formed structured `Syntax` value"}

  defp syntax_path_phrase([]), do: "the expansion root"
  defp syntax_path_phrase(path), do: "`#{format_syntax_path(path)}`"

  defp lift_module_failure(kind, details, opts) do
    {title, message, label, hint} = lift_module_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :lift_module_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp lift_module_content(:invalid_lift_module, _details),
    do:
      {"Lifted module request is malformed", "BEAM emission expected a validated lifted-module request.",
       "rewrite this lifted module request", "Build the request from a valid `lift module` declaration"}

  defp lift_module_content(:invalid_lift_module_ast, _details),
    do:
      {"Lifted module syntax is malformed",
       "A lifted module must be represented by one well-formed `lift_module` syntax node.",
       "rewrite this lifted module", "Use a `lift module` declaration with a name and body"}

  defp lift_module_content(:invalid_lift_module_name, %{detail: name}),
    do:
      {"Lifted module name is outside Cure",
       "The generated module `#{name_to_string(name)}` is not beneath the `Cure` namespace required for lifted code.",
       "move this module beneath `Cure`", "Use a module name beginning with `Cure.`"}

  defp lift_module_content(:invalid_module_name, %{detail: name}),
    do:
      {"Lifted module name is invalid",
       "`#{name_to_string(name)}` is not a valid qualified module name; every segment must begin with an uppercase letter.",
       "replace this lifted module name", "Use a name such as `Cure.Generated.Worker`"}

  defp lift_module_content(:invalid_behaviour, %{detail: behaviour}),
    do:
      {"Lifted module behaviour is invalid",
       "A lifted module needs a non-empty atom naming its BEAM behaviour, but this declaration uses `#{name_to_string(behaviour)}`.",
       "replace this behaviour", "Use the atom naming the implemented BEAM behaviour"}

  defp lift_module_content(:invalid_lift_callback, _details),
    do:
      {"Lifted module callback is malformed",
       "Every lifted callback needs an atom name, a non-negative arity, parameters, return type, body, and source line.",
       "rewrite this lifted callback", "Provide a complete callback declaration matching the behaviour"}

  defp lift_module_content(:invalid_lift_declaration, _details),
    do:
      {"Lifted module declaration is malformed",
       "Every declaration copied into a lifted module must be quoted Cure syntax.", "rewrite this lifted declaration",
       "Provide quoted declaration nodes in the lifted module body"}

  defp lift_module_content(:invalid_lift_import, _details),
    do:
      {"Lifted module import is malformed", "Every lifted-module dependency must be a textual qualified module name.",
       "rewrite this lifted import", "Use qualified import names such as `Std.Actor`"}

  defp lift_module_content(:invalid_lift_inheritance, _details),
    do:
      {"Lifted module inheritance option is invalid", "The `inherit_imports` option must be either `true` or `false`.",
       "replace this inheritance option", "Use `true` to inherit enclosing imports or `false` to isolate them"}

  defp lift_module_content(:lifted_module_dependency_cycle, %{detail: name}),
    do:
      {"Lifted modules form a dependency cycle",
       "The generated module `#{name_to_string(name)}` is reached again while ordering lifted-module dependencies.",
       "break this lifted-module cycle", "Remove or redirect one dependency in the cycle"}

  defp lift_module_content(:duplicate_lifted_module, %{detail: name}),
    do:
      {"Lifted module name is repeated",
       "More than one generated declaration produces `#{name_to_string(name)}`, so the compiler cannot choose one module body.",
       "rename one lifted module", "Give every lifted module a unique qualified name"}

  defp macro_raw_content(:missing_raw_delimiter, %{delimiter: delimiter}),
    do:
      {"Raw macro input is not terminated",
       "This raw macro capture reaches the end of its input without the `#{name_to_string(delimiter)}` delimiter.",
       "close this raw macro input", "Add the `#{name_to_string(delimiter)}` delimiter after the raw input"}

  defp macro_raw_content(:invalid_raw_delimiter, %{delimiter: delimiter}),
    do:
      {"Raw macro delimiter is invalid",
       "A raw macro delimiter must be text, but this capture uses `#{name_to_string(delimiter)}`.",
       "replace this raw delimiter", "Use a textual token or structural delimiter name"}

  defp macro_raw_content(:invalid_raw_tokens, _details),
    do:
      {"Raw macro token stream is malformed", "Raw macro capture expected a list of lexer tokens.",
       "replace this raw token stream", "Pass the lexer tokens belonging to the raw macro input"}

  defp macro_module_failure(kind, details, opts) do
    {title, message, label, hint} = macro_module_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_module_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: primary_label(opts, label),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp macro_family_failure(reason, opts) do
    Diagnostic.new(
      code: "E092",
      key: :invalid_macro_family,
      severity: :error,
      title: macro_family_title(reason),
      body: Doc.paragraph(macro_family_body(reason)),
      primary: primary_label(opts, macro_family_primary_label(reason)),
      suggestions: [%Suggestion{message: macro_family_hint(reason), applicability: :manual}],
      payload: %{reason: reason}
    )
  end

  defp macro_module_content(:module_rule_not_fully_consumed, _details),
    do:
      {"Module macro leaves input unconsumed",
       "This module macro expands one declaration but leaves additional authored tokens outside the matched rule.",
       "match the complete module-macro input", "Extend the rule to consume the remaining tokens or remove them"}

  defp macro_module_content(:not_a_module_rule, _details),
    do:
      {"Macro rule cannot expand a module",
       "This rule is being executed as a module macro, but it was not declared with module scope.",
       "use a module-scoped macro rule", "Declare this syntax as a module rule before executing it here"}

  defp macro_module_content(:invalid_module_rule_set, _details),
    do:
      {"Module macro rule set is malformed",
       "Module expansion needs a list containing valid syntax rules from the same macro.",
       "rewrite this module-macro rule set", "Provide the parsed syntax rules that own this module rule"}

  defp macro_module_content(:invalid_module_rule_bindings, _details),
    do:
      {"Module macro bindings are malformed",
       "Module-rule bindings must map each declared hole name to its captured syntax value.",
       "rewrite these module-macro bindings", "Provide a map from hole names to captured syntax"}

  defp macro_module_content(:invalid_macro_extension_rules, _details),
    do:
      {"Macro extension lists are malformed",
       "Open-category composition needs separate lists of base rules and extension rules.",
       "rewrite these macro extension lists", "Provide one list of base rules and one list of extension rules"}

  defp macro_module_content(:invalid_macro_extension_rule, _details),
    do:
      {"Macro extension rule is malformed", "Every base or extension rule must be a parsed macro-rule map.",
       "rewrite this macro extension rule", "Provide valid parsed macro rules in both lists"}

  defp macro_module_content(:closed_category_extension, %{categories: categories}) do
    rendered = Enum.map_join(categories, ", ", &"`#{name_to_string(&1)}`")

    {"Closed macro category cannot be extended",
     "The extension adds syntax to #{category_phrase(categories, rendered)}, but only categories declared open accept external rules.",
     "remove this closed-category extension", "Declare the category open or move the syntax into its owning macro"}
  end

  defp macro_module_content(:ambiguous_macro_extension, %{keywords: keywords}) do
    rendered = Enum.map_join(keywords, ", ", &"`#{name_to_string(&1)}`")

    {"Macro extension repeats a keyword",
     "The composed macro would contain multiple rules beginning with #{keyword_phrase(keywords, rendered)}, making dispatch ambiguous.",
     "rename this extension keyword", "Give each composed rule a distinct leading keyword"}
  end

  defp category_phrase([_one], rendered), do: "closed category #{rendered}"
  defp category_phrase(_many, rendered), do: "closed categories #{rendered}"

  defp keyword_phrase([_one], rendered), do: "keyword #{rendered}"
  defp keyword_phrase(_many, rendered), do: "keywords #{rendered}"

  defp macro_reducer_content(:invalid_reducer_arms, _details),
    do:
      {"Reducer arms are malformed", "Reducer arms must be provided as a list with one arm for every constructor.",
       "rewrite this reducer arm list", "Provide a list of constructor arms"}

  defp macro_reducer_content(:invalid_reducer_arm, _details),
    do:
      {"Reducer arm is malformed",
       "Every reducer arm needs a constructor, an optional list of text bindings, and a body expression.",
       "rewrite this reducer arm", "Provide `constructor`, `bindings`, and `body` for this arm"}

  defp macro_reducer_content(:duplicate_reducer_constructor, _details),
    do:
      {"Reducer constructor is repeated",
       "Two reducer arms match the same constructor, so one arm can never be selected.",
       "remove or change this duplicate arm", "Keep exactly one arm for each constructor"}

  defp macro_reducer_content(:unknown_reducer_constructor, %{constructors: constructors}) do
    rendered = Enum.map_join(constructors, ", ", &"`#{name_to_string(&1)}`")
    verb = if length(constructors) == 1, do: "does", else: "do"

    {"Reducer uses an unknown constructor",
     "The reducer refers to #{constructor_phrase(constructors, rendered)}, which #{verb} not belong to the reflected data type.",
     "replace this unknown constructor", "Use only constructors declared by the reduced data type"}
  end

  defp macro_reducer_content(:incomplete_reducer, %{constructors: constructors}) do
    rendered = Enum.map_join(constructors, ", ", &"`#{name_to_string(&1)}`")

    {"Reducer does not cover every constructor",
     "The reducer has no arm for #{constructor_phrase(constructors, rendered)}.", "add the missing constructor arm",
     "Add one arm for every listed constructor"}
  end

  defp macro_reducer_content(:reducer_arity, %{constructor: constructor, actual: actual, expected: expected}),
    do:
      {"Reducer arm has the wrong number of bindings",
       "The `#{name_to_string(constructor)}` arm binds #{actual} values, but its constructor carries #{expected}.",
       "make these bindings match the constructor", "Use exactly #{expected} bindings in this arm"}

  defp constructor_phrase([_one], rendered), do: "constructor #{rendered}"
  defp constructor_phrase(_many, rendered), do: "constructors #{rendered}"

  defp macro_parse_content(:invalid_parse_name, %{name: name}),
    do:
      {"Parser grammar name is invalid",
       "A generated parser grammar needs an atom or text name, but this grammar uses `#{name_to_string(name)}`.",
       "replace this grammar name", "Use a stable grammar name such as `Command`"}

  defp macro_parse_content(:invalid_parse_productions, _details),
    do:
      {"Parser productions are malformed", "A parser grammar's productions must be provided as an ordered list.",
       "rewrite this production list", "Provide a list of named parser productions"}

  defp macro_parse_content(:invalid_parse_production, _details),
    do:
      {"Parser production is malformed",
       "Every parser production needs an atom or text name and a non-empty body of token or production names.",
       "rewrite this parser production", "Provide `name` and a non-empty `body` list"}

  defp macro_parse_content(:duplicate_parse_production, _details),
    do:
      {"Parser production name is repeated",
       "Two productions in this grammar have the same name, so references to that production would be ambiguous.",
       "rename or remove this production", "Give every production in the grammar a unique name"}

  defp macro_parse_content(:left_recursive_parse_production, %{names: names}) do
    rendered = Enum.map_join(names, ", ", &"`#{name_to_string(&1)}`")
    {verb, reflexive} = if length(names) == 1, do: {"begins", "itself"}, else: {"begin", "themselves"}

    {"Parser production is left-recursive",
     "#{rendered} #{verb} by invoking #{reflexive}, so recursive descent would make no progress before recurring.",
     "remove this leading self-reference", "Rewrite the production so it consumes a token before recurring"}
  end

  defp macro_protocol_content(:invalid_protocol_name, %{name: name}),
    do:
      {"Protocol name is invalid",
       "A protocol name must be an atom or text, but this definition uses `#{name_to_string(name)}`.",
       "replace this protocol name", "Use a stable protocol name such as `Provisioning`"}

  defp macro_protocol_content(:invalid_protocol_roles, _details),
    do:
      {"Protocol roles are malformed",
       "A protocol's roles must be written as a list containing its two endpoint names.", "rewrite this role list",
       "Provide exactly two distinct atom role names"}

  defp macro_protocol_content(:protocol_role_count, %{count: count}) do
    noun = if count == 1, do: "role", else: "roles"

    {"Protocol needs exactly two roles",
     "This two-party protocol declares #{count} #{noun}, but it must declare exactly two.",
     "make this a two-party protocol", "Keep exactly two distinct role names"}
  end

  defp macro_protocol_content(:invalid_protocol_role, _details),
    do:
      {"Protocol role name is invalid",
       "Every protocol role must be an atom so generated endpoint names remain stable.", "replace this role name",
       "Use atom role names such as `client` and `server`"}

  defp macro_protocol_content(:duplicate_protocol_role, _details),
    do:
      {"Protocol role is repeated",
       "Both endpoints have the same role name, so sends and receives cannot identify opposite parties.",
       "rename one protocol role", "Give the two endpoints distinct role names"}

  defp macro_protocol_content(:invalid_protocol_steps, _details),
    do:
      {"Protocol steps are malformed", "A protocol's message flow must be a list of ordered send steps.",
       "rewrite this step list", "Provide a list of steps with `sender`, `receiver`, and `message`"}

  defp macro_protocol_content(:invalid_protocol_step, _details),
    do:
      {"Protocol step is malformed", "Every protocol step needs both a sender and a receiver from this protocol.",
       "rewrite this protocol step", "Provide `sender`, `receiver`, and `message` for this step"}

  defp macro_protocol_content(:unknown_protocol_role, %{sender: sender, receiver: receiver}),
    do:
      {"Protocol step uses an unknown role",
       "The step from `#{name_to_string(sender)}` to `#{name_to_string(receiver)}` names an endpoint outside this protocol.",
       "use the declared protocol roles", "Choose both endpoints from the protocol's two declared roles"}

  defp macro_protocol_content(:self_protocol_step, %{role: role}),
    do:
      {"Protocol step sends to itself",
       "The `#{name_to_string(role)}` endpoint is both sender and receiver in this step.",
       "choose the opposite receiver", "Send each message from one role to the other"}

  defp macro_protocol_content(:invalid_protocol_message, _details),
    do:
      {"Protocol message is missing", "This step has no message for its sender to transmit to its receiver.",
       "add this step's message", "Add a message declaration to this protocol step"}

  defp macro_protocol_content(:invalid_protocol_options, _details),
    do:
      {"Protocol options are malformed",
       "Protocol options must be a keyword list containing optional choices and timeout settings.",
       "rewrite these protocol options", "Use keyword options such as `choices: [...]` or `timeout: 1000`"}

  defp macro_protocol_content(:invalid_protocol_choices, _details),
    do:
      {"Protocol choices are malformed", "The protocol's choices must be a list of branching decisions.",
       "rewrite this choice list", "Provide a list of choices with `decider` and non-empty `branches`"}

  defp macro_protocol_content(:invalid_protocol_choice, _details),
    do:
      {"Protocol choice is malformed",
       "Every protocol choice needs the role that decides it and its possible branches.",
       "rewrite this protocol choice", "Provide `decider` and a non-empty `branches` list"}

  defp macro_protocol_content(:unknown_choice_decider, %{role: role}),
    do:
      {"Protocol choice has an unknown decider",
       "The `#{name_to_string(role)}` role decides this choice but is not an endpoint in the protocol.",
       "use a declared role as decider", "Choose one of the protocol's two roles as the decider"}

  defp macro_protocol_content(:invalid_protocol_branches, %{role: role}),
    do:
      {"Protocol choice has no valid branches",
       "The choice decided by `#{name_to_string(role)}` needs a non-empty list of protocol-step branches.",
       "add the possible branches", "Provide at least one branch beginning with a send from the decider"}

  defp macro_protocol_content(:unprojectable_choice, %{role: role}),
    do:
      {"Protocol choice cannot be projected",
       "Every branch decided by `#{name_to_string(role)}` must begin with that role sending a message, so the other endpoint can observe the choice.",
       "make the decider announce each branch", "Start every branch with a message sent by `#{name_to_string(role)}`"}

  defp macro_check_content(:invalid_check_name, %{name: name}) do
    {
      "Check plan name is invalid",
      "A generated check plan needs an atom or text name, but this plan uses `#{name_to_string(name)}`.",
      "replace this check plan name",
      "Use a stable name such as `FrameProperties`"
    }
  end

  defp macro_check_content(:invalid_check_property, _details) do
    {
      "Check property is malformed",
      "Every check property needs a name, a supported check kind, and the expression to test.",
      "rewrite this check property",
      "Provide `name`, `kind`, and `expression`; use `round_trip`, `total`, `fault_rejection`, `exhaustive`, or `termination`"
    }
  end

  defp macro_check_content(:duplicate_check_property, _details) do
    {
      "Check property name is repeated",
      "Two properties in this check plan have the same name, so their generated results cannot be distinguished.",
      "rename or remove this property",
      "Give every property in the check plan a unique name"
    }
  end

  defp macro_unit_content(:duplicate_unit, %{suffix: suffix}) do
    {
      "Unit suffix is already declared",
      "The `#{name_to_string(suffix)}` suffix is registered more than once, so a literal would have two possible scales.",
      "rename or remove this unit declaration",
      "Keep exactly one declaration for the `#{name_to_string(suffix)}` suffix"
    }
  end

  defp macro_unit_content(:invalid_unit, %{suffix: suffix}) do
    {
      "Unit declaration is invalid",
      "The `#{name_to_string(suffix)}` unit needs a text suffix, a positive numeric scale, and an atom naming its dimension.",
      "fix this unit declaration",
      "Use a positive scale and a stable dimension such as `duration`"
    }
  end

  defp macro_unit_content(:unknown_unit, %{suffix: suffix}) do
    {
      "Unit suffix is unknown",
      "The `#{name_to_string(suffix)}` suffix is used by this literal, but no unit with that suffix is registered.",
      "declare this unit or change the suffix",
      "Register `#{name_to_string(suffix)}` before using it in a literal"
    }
  end

  defp macro_unit_content(:invalid_unit_literal, %{value: value, suffix: suffix}) do
    {
      "Unit literal is malformed",
      "A unit literal needs a numeric value and a text suffix, but this one uses value `#{name_to_string(value)}` and suffix `#{name_to_string(suffix)}`.",
      "rewrite this unit literal",
      "Use a number followed by a registered text suffix"
    }
  end

  defp macro_board_content(:invalid_board_definition, _details) do
    {
      "Board definition is malformed",
      "A board definition must be a map containing its chip, pins, capabilities, buses, and flash layout.",
      "rewrite this board definition",
      "Provide a board definition map with `chip`, `pins`, `capabilities`, `buses`, and `flash`"
    }
  end

  defp macro_board_content(:invalid_board_name, %{detail: name}) do
    {
      "Board name is invalid",
      "A board name must be an atom or string, but this definition uses `#{name_to_string(name)}`.",
      "replace this board name",
      "Use a stable board name such as `Esp32c3`"
    }
  end

  defp macro_board_content(:missing_board_chip, _details) do
    {
      "Board chip is missing",
      "The board definition does not identify the chip that owns its pins and peripherals.",
      "add this board's chip",
      "Add a `chip` entry such as `chip: :esp32c3`"
    }
  end

  defp macro_board_content(:invalid_board_chip, %{detail: chip}) do
    {
      "Board chip is invalid",
      "A chip identifier must be an atom or string, but this definition uses `#{name_to_string(chip)}`.",
      "replace this chip identifier",
      "Use a stable chip identifier such as `esp32c3`"
    }
  end

  defp macro_board_content(:invalid_board_pins, _details) do
    {
      "Board pin set is invalid",
      "Pins must be a non-negative inclusive range or a list of non-negative pin numbers.",
      "fix this pin set",
      "Use `{first, last}` or a list such as `[0, 1, 2]`"
    }
  end

  defp macro_board_content(:unknown_board_pin, %{detail: pin}) do
    {
      "Capability refers to an unknown board pin",
      "Pin `#{name_to_string(pin)}` has capabilities here, but it is not present in the board's pin set.",
      "declare this pin or remove its capabilities",
      "Add pin `#{name_to_string(pin)}` to `pins`, or remove this capability entry"
    }
  end

  defp macro_board_content(:invalid_board_capability, %{detail: pin}) do
    {
      "Board pin has an invalid capability",
      "Pin `#{name_to_string(pin)}` has a capability outside the supported GPIO, analog, strapping, USB, and touch set.",
      "fix this pin's capabilities",
      "Use only `input`, `output`, `adc`, `dac`, `strapping`, `usb`, or `touch`"
    }
  end

  defp macro_board_content(:invalid_board_capabilities, _details) do
    {
      "Board capabilities are malformed",
      "Board capabilities must be a map from each pin number to a list of supported capabilities.",
      "rewrite this capability map",
      "Map each pin to its capabilities, for example pin `8` to `input` and `output`"
    }
  end

  defp macro_board_content(:invalid_board_bus, %{detail: bus}) do
    {
      "Board bus wiring is invalid",
      "The `#{name_to_string(bus)}` bus needs an atom name and a map from signal names to pin numbers.",
      "rewrite this bus wiring",
      "Map each signal to its pin, for example `sda` to `8` and `scl` to `9`"
    }
  end

  defp macro_board_content(:unknown_bus_pin, %{detail: bus}) do
    {
      "Board bus uses an unknown pin",
      "The `#{name_to_string(bus)}` bus assigns at least one pin that is not present in the board's pin set.",
      "fix this bus pin assignment",
      "Assign every `#{name_to_string(bus)}` signal to a pin declared by `pins`"
    }
  end

  defp macro_board_content(:missing_bus_capability, %{detail: bus}) do
    {
      "Board bus pin has no capability declaration",
      "The `#{name_to_string(bus)}` bus uses a declared pin whose capabilities are missing, so generated peripheral checks cannot validate it.",
      "declare capabilities for every bus pin",
      "Add each `#{name_to_string(bus)}` pin to the `capabilities` map"
    }
  end

  defp macro_board_content(:invalid_board_buses, _details) do
    {
      "Board bus table is malformed",
      "Board buses must be a map from bus names to signal-to-pin wiring maps.",
      "rewrite this bus table",
      "Map each bus name to its signal-to-pin wiring"
    }
  end

  defp macro_board_content(:invalid_board_flash, _details) do
    {
      "Board flash layout is malformed",
      "Flash layout needs a positive total size and non-negative application and library offsets.",
      "fix this flash layout",
      "Provide integer `size`, `app_offset`, and `libs_offset` values"
    }
  end

  defp macro_board_content(:flash_offset_out_of_bounds, _details) do
    {
      "Board flash offset is outside the device",
      "The application or library partition starts at or beyond the declared flash size.",
      "move this partition inside flash",
      "Choose `app_offset` and `libs_offset` values smaller than `size`"
    }
  end

  defp macro_driver_content(:invalid_driver_base, %{base: base}) do
    {
      "Driver base address is invalid",
      "A driver base address must be a non-negative integer, but this definition uses `#{name_to_string(base)}`.",
      "replace this base address",
      "Use the non-negative byte address where this device's register block begins"
    }
  end

  defp macro_driver_content(:invalid_driver_register, _details) do
    {
      "Driver register is malformed",
      "Every register needs a name, a non-negative byte offset, an 8-, 16-, or 32-bit width, and `read`, `write`, or `read_write` access.",
      "rewrite this register declaration",
      "Provide `name`, `offset`, `width`, and `access` for every register"
    }
  end

  defp macro_driver_content(:duplicate_driver_register, _details) do
    {
      "Driver register name is repeated",
      "Two registers have the same name, so generated accessors would collide.",
      "rename or remove this repeated register",
      "Give every register a unique name"
    }
  end

  defp macro_driver_content(:overlapping_driver_register, _details) do
    {
      "Driver register ranges overlap",
      "Two registers occupy at least one of the same bytes in the device register map.",
      "move or resize one of these registers",
      "Choose offsets and widths whose byte ranges do not overlap"
    }
  end

  defp macro_packet_content(:invalid_packet_name, %{detail: name}) do
    {
      "Packet name is invalid",
      "A packet name must be an atom or string, but this declaration uses `#{name_to_string(name)}`.",
      "replace this packet name",
      "Use a stable packet name such as `Frame`"
    }
  end

  defp macro_packet_content(:invalid_packet_endian, %{detail: endian}) do
    {
      "Packet byte order is invalid",
      "`#{name_to_string(endian)}` is not a packet byte order. Multi-byte scalar fields use big-endian (`be`) or little-endian (`le`) order.",
      "choose a supported byte order",
      "Use `endian: :be` or `endian: :le`"
    }
  end

  defp macro_packet_content(:unknown_packet_scalar, %{detail: scalar}) do
    {
      "Packet scalar type is unknown",
      "`#{name_to_string(scalar)}` is not a fixed-width packet scalar.",
      "replace this scalar type",
      "Use one of `u8`, `i8`, `u16`, `i16`, `u32`, `i32`, or `byte`"
    }
  end

  defp macro_packet_content(:missing_packet_endian, %{detail: field}) do
    {
      "Packet field needs a byte order",
      "The multi-byte `#{name_to_string(field)}` field has no byte order, so its encoded bytes would be ambiguous.",
      "declare this field's byte order",
      "Set `endian: :be` or `endian: :le` on the packet or this field"
    }
  end

  defp macro_packet_content(:forward_packet_length, %{field: field, dependency: length_field}) do
    {
      "Packet length field comes too late",
      "The `#{name_to_string(field)}` field takes its length from `#{name_to_string(length_field)}`, but that length field has not been decoded yet.",
      "move the length field before this payload",
      "Declare `#{name_to_string(length_field)}` before `#{name_to_string(field)}`"
    }
  end

  defp macro_packet_content(:invalid_packet_crc_fields, %{field: field, dependency: missing}) do
    names = missing |> List.wrap() |> Enum.map_join(", ", &"`#{name_to_string(&1)}`")

    {
      "Packet checksum references unavailable fields",
      "The `#{name_to_string(field)}` checksum includes #{names}, but those fields have not been decoded before the checksum.",
      "fix this checksum coverage",
      "List only earlier packet fields in `over`, or move the referenced fields before `#{name_to_string(field)}`"
    }
  end

  defp macro_packet_content(:duplicate_packet_field, _details) do
    {
      "Packet field name is repeated",
      "Two packet fields have the same name, so generated accessors and layout entries would collide.",
      "rename or remove this repeated field",
      "Give every packet field a unique name"
    }
  end

  defp macro_packet_content(:invalid_packet_field_name, _details) do
    {
      "Packet field has no name",
      "Every packet field needs a name so later length and checksum fields can refer to it.",
      "add a name to this field",
      "Add a unique `name` to every packet field"
    }
  end

  defp macro_packet_content(:invalid_packet_field, _details) do
    {
      "Packet field is malformed",
      "A packet field must declare a name and one supported shape: constant, scalar, bytes, or checksum.",
      "rewrite this packet field",
      "Use a `const`, `scalar`, `bytes`, or `crc` field with all required properties"
    }
  end

  defp macro_validation_failure(kind, details, opts, context) do
    span = Map.get(context, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :macro_validation_failed,
      severity: :error,
      title: macro_validation_title(kind),
      body: Doc.paragraph(macro_validation_message(kind, details)),
      primary: pickup_label(span, :primary, macro_validation_primary_label(kind)),
      secondary: macro_validation_secondary_labels(kind, context, span),
      suggestions: macro_validation_suggestions(kind),
      payload: %{kind: kind, details: details, macro: Map.get(context, :macro)}
    )
  end

  defp macro_validation_title(:missing_diagnosis), do: "Macro explanations are incomplete"
  defp macro_validation_title(:rule_unpinned), do: "Macro rule needs a worked example"
  defp macro_validation_title(:example_mismatch), do: "Macro example has the wrong expansion"
  defp macro_validation_title(:example_type_mismatch), do: "Macro example has the wrong type"
  defp macro_validation_title(:computed_example_error), do: "Computed macro example failed"
  defp macro_validation_title(:reserved_syntax_field), do: "Macro hole uses a reserved name"
  defp macro_validation_title(:unsupported_hole_type), do: "Macro hole cannot be generated for proofs"
  defp macro_validation_title(_kind), do: "Macro validation failed"

  defp macro_validation_primary_label(:missing_diagnosis), do: "add clauses for the unexplained failure points"
  defp macro_validation_primary_label(:rule_unpinned), do: "add a worked example beneath this rule"
  defp macro_validation_primary_label(:example_mismatch), do: "this pin does not match the actual expansion"
  defp macro_validation_primary_label(:example_type_mismatch), do: "this pinned type does not accept the expansion"
  defp macro_validation_primary_label(:computed_example_error), do: "this computed example could not be checked"
  defp macro_validation_primary_label(:reserved_syntax_field), do: "this hole name is reserved for expansion context"
  defp macro_validation_primary_label(:unsupported_hole_type), do: "the proof generator cannot construct this category"
  defp macro_validation_primary_label(_kind), do: "this macro declaration is incomplete or inconsistent"

  defp macro_validation_secondary_labels(:missing_diagnosis, context, primary_span) do
    context
    |> Map.get(:rule_spans, [])
    |> Enum.map(&pickup_label(&1, :secondary, "this rule declares an unexplained failure point"))
    |> Enum.reject(&(&1.span == primary_span))
  end

  defp macro_validation_secondary_labels(:rule_unpinned, context, primary_span) do
    context
    |> Map.get(:rule_spans, [])
    |> Enum.drop(1)
    |> Enum.map(&pickup_label(&1, :secondary, "this rule also needs a worked example"))
    |> Enum.reject(&(&1.span == primary_span))
  end

  defp macro_validation_secondary_labels(kind, context, primary_span)
       when kind in [:example_mismatch, :example_type_mismatch, :computed_example_error] do
    context
    |> Map.get(:rule_spans, [])
    |> Enum.map(&pickup_label(&1, :secondary, "this rule owns the failing example"))
    |> Enum.reject(&(&1.span == primary_span))
  end

  defp macro_validation_secondary_labels(:reserved_syntax_field, context, primary_span) do
    context
    |> Map.get(:hole_spans, [])
    |> Enum.map(&pickup_label(&1, :secondary, "this hole also uses the reserved context name"))
    |> Enum.reject(&(&1.span == primary_span))
  end

  defp macro_validation_secondary_labels(:unsupported_hole_type, context, primary_span) do
    context
    |> Map.get(:hole_spans, [])
    |> Enum.map(&pickup_label(&1, :secondary, "this hole uses the same unsupported category"))
    |> Enum.reject(&(&1.span == primary_span))
  end

  defp macro_validation_secondary_labels(_kind, _context, _primary_span), do: []

  defp macro_validation_suggestions(:missing_diagnosis),
    do: [%Suggestion{message: "Add one `explain` clause for each listed failure point", applicability: :manual}]

  defp macro_validation_suggestions(:rule_unpinned),
    do: [
      %Suggestion{message: "Add `example use_site expands expected` beneath each listed rule", applicability: :manual}
    ]

  defp macro_validation_suggestions(:example_mismatch),
    do: [%Suggestion{message: "Update the pinned expansion or fix the macro rule", applicability: :manual}]

  defp macro_validation_suggestions(:example_type_mismatch),
    do: [%Suggestion{message: "Use the expansion's actual type or fix the macro rule", applicability: :manual}]

  defp macro_validation_suggestions(:computed_example_error),
    do: [%Suggestion{message: "Fix the computed expander or its worked example", applicability: :manual}]

  defp macro_validation_suggestions(:reserved_syntax_field),
    do: [%Suggestion{message: "Rename this hole; `context` is supplied automatically", applicability: :manual}]

  defp macro_validation_suggestions(:unsupported_hole_type),
    do: [
      %Suggestion{
        message: "Use a generatable category, or mark the rule `contextual` when proof needs its call site",
        applicability: :manual
      }
    ]

  defp macro_validation_suggestions(_kind), do: []

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

  defp macro_validation_message(:reserved_syntax_field, %{first: field, second: keywords}),
    do:
      "The hole `#{field}` in #{macro_rule_names(keywords)} conflicts with the reflected expansion context supplied to computed rules."

  defp macro_validation_message(:unsupported_hole_type, %{detail: category}),
    do:
      "The generative expansion proof has no safe value generator for the `#{name_to_string(category)}` hole category."

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

  defp macro_family_title({:unknown_syntax_family, _name}), do: "Included syntax family is unknown"
  defp macro_family_title({:syntax_family_cycle, _names}), do: "Syntax families form a cycle"
  defp macro_family_title({:duplicate_syntax_family, _names}), do: "Syntax family name is repeated"
  defp macro_family_title({:duplicate_syntax_family_field, _pairs}), do: "Syntax-family field is duplicated"
  defp macro_family_title(:invalid_macro_rules), do: "Macro rule list is malformed"
  defp macro_family_title(:expander_without_accepts), do: "Macro expander has no accepted family"
  defp macro_family_title(:accepts_without_syntax_family), do: "Accepted syntax family is not declared"
  defp macro_family_title(:accepts_without_expander), do: "Accepted syntax family has no expander"
  defp macro_family_title(:multiple_accepts_declarations), do: "Macro accepts more than one family"
  defp macro_family_title(:multiple_expands_declarations), do: "Macro declares more than one expander"
  defp macro_family_title(_reason), do: "Syntax-family declaration is invalid"

  defp macro_family_body({:unknown_syntax_family, name}),
    do: "`#{name}` is included here, but this macro does not declare a syntax family with that name."

  defp macro_family_body({:syntax_family_cycle, names}),
    do: "These syntax families include one another in a cycle: #{Enum.map_join(names, " → ", &to_string/1)}."

  defp macro_family_body({:duplicate_syntax_family, names}),
    do:
      "The same syntax family name is declared more than once: #{Enum.map_join(names, ", ", &"`#{name_to_string(&1)}`")}."

  defp macro_family_body({:duplicate_syntax_family_field, pairs}) do
    fields = Enum.map_join(pairs, ", ", fn {family, field} -> "`#{family}.#{field}`" end)
    "The same field is declared more than once: #{fields}."
  end

  defp macro_family_body(:invalid_macro_rules),
    do: "Structured macro validation expected a list of well-formed macro rules."

  defp macro_family_body(:expander_without_accepts),
    do: "This macro declares how to expand a syntax family but never declares which family it accepts."

  defp macro_family_body(:accepts_without_syntax_family),
    do: "This macro accepts a syntax family but does not declare any syntax-family shape for that input."

  defp macro_family_body(:accepts_without_expander),
    do: "This macro accepts structured syntax but does not declare the function that expands it."

  defp macro_family_body(:multiple_accepts_declarations),
    do: "A structured macro can have only one `accepts` declaration, but this macro has more than one."

  defp macro_family_body(:multiple_expands_declarations),
    do: "A structured macro can have only one `expands with` declaration, but this macro has more than one."

  defp macro_family_body(reason),
    do: "The syntax-family declarations are inconsistent: #{name_to_string(reason)}."

  defp macro_family_primary_label({:unknown_syntax_family, _name}), do: "this included family is not declared"
  defp macro_family_primary_label({:syntax_family_cycle, _names}), do: "the inclusion cycle starts here"
  defp macro_family_primary_label({:duplicate_syntax_family, _names}), do: "this family name is declared again"
  defp macro_family_primary_label({:duplicate_syntax_family_field, _pairs}), do: "this field is declared again"
  defp macro_family_primary_label(:invalid_macro_rules), do: "rewrite these macro rules"
  defp macro_family_primary_label(:expander_without_accepts), do: "this expander has no matching `accepts` declaration"
  defp macro_family_primary_label(:accepts_without_syntax_family), do: "this accepted family has no declaration"
  defp macro_family_primary_label(:accepts_without_expander), do: "this accepted family has no expander"
  defp macro_family_primary_label(:multiple_accepts_declarations), do: "remove this additional `accepts` declaration"
  defp macro_family_primary_label(:multiple_expands_declarations), do: "remove this additional expander declaration"
  defp macro_family_primary_label(_reason), do: "this macro family is inconsistent"

  defp macro_family_related_label({:syntax_family_cycle, _names}), do: "this family also participates in the cycle"
  defp macro_family_related_label({:duplicate_syntax_family, _names}), do: "the family name was first declared here"
  defp macro_family_related_label({:duplicate_syntax_family_field, _pairs}), do: "the field was already declared here"
  defp macro_family_related_label(:multiple_accepts_declarations), do: "another `accepts` declaration is here"
  defp macro_family_related_label(:multiple_expands_declarations), do: "another expander declaration is here"
  defp macro_family_related_label(_reason), do: "related family declaration"

  defp macro_family_hint({:unknown_syntax_family, name}),
    do: "Declare `syntax family #{name}` or change `includes` to a declared family"

  defp macro_family_hint({:syntax_family_cycle, _names}),
    do: "Remove one `includes` edge so the family graph is acyclic"

  defp macro_family_hint({:duplicate_syntax_family, _names}),
    do: "Rename one family or combine their fields into a single declaration"

  defp macro_family_hint({:duplicate_syntax_family_field, _pairs}),
    do: "Keep one declaration of the field"

  defp macro_family_hint(:invalid_macro_rules), do: "Provide a list of parsed macro rules"
  defp macro_family_hint(:expander_without_accepts), do: "Add `accepts FamilyName` for the expander's input"
  defp macro_family_hint(:accepts_without_syntax_family), do: "Declare the accepted family with `syntax family`"
  defp macro_family_hint(:accepts_without_expander), do: "Add `expands with function_name`"
  defp macro_family_hint(:multiple_accepts_declarations), do: "Keep exactly one `accepts` declaration"
  defp macro_family_hint(:multiple_expands_declarations), do: "Keep exactly one `expands with` declaration"

  defp macro_family_hint(_reason), do: "Make the syntax-family declarations consistent"

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

  defp macro_rule_names([keyword]), do: "the `#{name_to_string(keyword)}` rule"

  defp macro_rule_names(keywords) when is_list(keywords) do
    "the #{Enum.map_join(keywords, ", ", &"`#{name_to_string(&1)}`")} rules"
  end

  @spec unknown_name(atom(), term(), keyword()) :: Diagnostic.t()
  def unknown_name(namespace, name, opts \\ []),
    do: NameAdapter.unknown_name(namespace, name, opts)

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

  defp named_argument_primary(details, opts, message) do
    index = named_argument_index(details)
    span = Enum.at(Map.get(details, :label_spans, []), index) || Enum.at(Map.get(details, :argument_spans, []), index)

    case span || Keyword.get(opts, :span) do
      %Span{} = primary -> %Label{span: primary, style: :primary, message: message}
      _ -> nil
    end
  end

  defp named_argument_labels(details) do
    primary_index = named_argument_index(details)
    label = Map.get(details, :label)

    duplicate_labels =
      details
      |> Map.get(:written, [])
      |> List.wrap()
      |> Enum.with_index()
      |> Enum.flat_map(fn
        {^label, index} when index != primary_index ->
          case Enum.at(Map.get(details, :label_spans, []), index) do
            %Span{} = span -> [%Label{span: span, style: :secondary, message: "`#{label}` is also supplied here"}]
            _ -> []
          end

        _ ->
          []
      end)

    argument_label =
      case Enum.at(Map.get(details, :argument_spans, []), primary_index) do
        %Span{} = span -> [%Label{span: span, style: :secondary, message: "argument value"}]
        _ -> []
      end

    parameter_labels =
      Map.get(details, :parameter_spans, [])
      |> Enum.flat_map(fn
        %Span{} = span -> [%Label{span: span, style: :secondary, message: "parameter declared here"}]
        _ -> []
      end)

    duplicate_labels ++ argument_label ++ parameter_labels
  end

  defp named_argument_index(%{argument_index: index}) when is_integer(index), do: index
  defp named_argument_index(%{parameter_index: index, written: nil}) when is_integer(index), do: index

  defp named_argument_index(details) do
    written = Map.get(details, :written) || []
    label = Map.get(details, :label)
    Enum.find_index(written, &(&1 == label)) || 0
  end

  defp named_argument_suggestions(:missing_label, %{label: label} = details) when is_binary(label) do
    index = named_argument_index(details)
    written = Map.get(details, :written)

    case {written == nil or Enum.at(written, index) == nil, Enum.at(Map.get(details, :argument_spans, []), index)} do
      {true, %Span{} = span} ->
        insertion = %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column}

        [
          %Suggestion{
            message: "Add the required `#{label}:` argument name",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: insertion, replacement: "#{label}: "}]
          }
        ]

      _ ->
        []
    end
  end

  defp named_argument_suggestions(:unknown_label, %{label: bad, telescope: telescope} = details)
       when is_binary(bad) do
    declared =
      telescope
      |> Enum.map(fn {_kind, name} -> name end)
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq()

    case {declared, Enum.at(Map.get(details, :label_spans, []), named_argument_index(details))} do
      {[replacement], %Span{} = span} ->
        [
          %Suggestion{
            message: "Replace `#{bad}` with the declared argument name `#{replacement}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: replacement}]
          }
        ]

      _ ->
        []
    end
  end

  defp named_argument_suggestions(_variant, _details), do: []

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

  defp simplification_labels(problem, primary) do
    [{problem.command, "simplify command"}, {problem.rule, "rule supplied here"}]
    |> Enum.flat_map(fn
      {%Span{} = span, message} when span != primary -> [%Label{span: span, style: :secondary, message: message}]
      _ -> []
    end)
  end

  defp induction_primary(problem, opts, message) do
    span =
      problem.pattern_range || problem.case_range || problem.subject_range || problem.construct ||
        Keyword.get(opts, :span)

    if match?(%Span{}, span), do: %Label{span: span, style: :primary, message: message}, else: nil
  end

  defp induction_labels(problem) do
    [
      {problem.subject_range, "induction subject"},
      {problem.constructor_range, "constructor declared here"},
      {problem.hypothesis_range, "induction hypothesis used here"}
    ]
    |> Enum.flat_map(fn
      {%Span{} = span, message} -> [%Label{span: span, style: :secondary, message: message}]
      _ -> []
    end)
  end

  defp induction_message(message, %InductionProblem{kind: :missing_case, missing: missing}) do
    message <> " Missing: " <> Enum.map_join(List.wrap(missing), ", ", &Cure.Elab.Name.base/1) <> "."
  end

  defp induction_message(message, %InductionProblem{kind: :wrong_case_fields} = problem) do
    message <>
      " Expected #{problem.expected_fields} bindings but found #{problem.observed_fields}; recursive fields at positions " <>
      Enum.map_join(List.wrap(problem.recursive_fields), ", ", &Integer.to_string(&1 + 1)) <> " produce hypotheses."
  end

  defp induction_message(message, %InductionProblem{kind: :mistyped_hypothesis} = problem) do
    message <>
      " Available: #{surface_type(problem.available)}. Required here: #{surface_type(problem.required)}."
  end

  defp induction_message(message, _problem), do: message

  defp induction_suggestions(%InductionProblem{
         kind: :missing_case,
         missing_case_skeletons: skeletons,
         insertion: %Span{} = insertion,
         case_indent: case_indent
       })
       when is_list(skeletons) and skeletons != [] do
    indent = String.duplicate(" ", max(case_indent || 0, 0))
    replacement = "\n" <> Enum.map_join(skeletons, "\n", &(indent <> &1))

    [
      %Suggestion{
        message: "Add missing induction cases",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: insertion, replacement: replacement}]
      }
    ]
  end

  defp induction_suggestions(%InductionProblem{kind: :missing_case, missing: missing}) do
    [
      %Suggestion{
        message: "Add cases for " <> Enum.map_join(List.wrap(missing), ", ", &Cure.Elab.Name.base/1),
        applicability: :manual,
        edits: []
      }
    ]
  end

  defp induction_suggestions(_problem), do: []

  defp simplification_body(message, problem, opts) do
    goals =
      if problem.before_surface && problem.after_surface do
        "\n\nBefore: #{problem.before_surface}\nAfter: #{problem.after_surface}"
      else
        ""
      end

    supplied =
      if problem.kind == :proof_mismatch and problem.simplified_supplied_surface do
        "\nSupplied proof simplifies to: #{problem.simplified_supplied_surface}"
      else
        ""
      end

    if Keyword.get(opts, :trace) == :expanded and (problem.trace_ids || []) != [] do
      ids = Enum.map_join(problem.trace_ids, ", ", &to_string/1)
      Doc.paragraph(message <> goals <> supplied <> "\n\nSimplification trace: " <> ids)
    else
      Doc.paragraph(message <> goals <> supplied)
    end
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

  defp rewrite_suggestions(%RewriteProblem{
         kind: :reverse_only,
         direction: direction,
         direction_range: %Span{} = direction_range
       }) do
    {span, replacement} =
      case direction do
        :forward ->
          {%Span{
             direction_range
             | start_byte: direction_range.end_byte,
               start_line: direction_range.end_line,
               start_column: direction_range.end_column
           }, " backwards"}

        :backwards ->
          {direction_range, ""}
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

  defp pickup_spans(spans), do: Enum.filter(spans, &match?(%Span{}, &1))

  defp pickup_label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp pickup_label(_, _style, _message), do: nil

  defp edition_replacement_suggestion(%{
         argument_span: %Span{} = span,
         known_editions: [edition],
         single_line: true
       }) do
    [
      %Suggestion{
        message: "Use the supported edition `#{edition}`",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: inspect(edition)}]
      }
    ]
  end

  defp edition_replacement_suggestion(%{known_editions: editions}) when is_list(editions) do
    [
      %Suggestion{
        message: "Use one of the supported editions: #{Enum.map_join(editions, ", ", &"`#{&1}`")}",
        applicability: :manual
      }
    ]
  end

  defp edition_replacement_suggestion(_details), do: []

  defp grade_suggestions(%{grade: grade, supported: supported}, %Span{} = span) do
    spelling = to_string(grade)

    ranked =
      supported
      |> Enum.map(&{&1, Suggest.distance(spelling, to_string(&1))})
      |> Enum.sort_by(fn {candidate, distance} -> {distance, to_string(candidate)} end)

    case ranked do
      [{candidate, distance}, {_other, next_distance} | _] when distance <= 2 and distance < next_distance ->
        [
          %Suggestion{
            message: "Replace it with `:#{candidate}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: ":#{candidate}"}]
          }
        ]

      [{candidate, distance}] when distance <= 2 ->
        [
          %Suggestion{
            message: "Replace it with `:#{candidate}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: ":#{candidate}"}]
          }
        ]

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

  defp syntax_family_field_suggestions(%{field: field, valid_fields: fields}, %Span{} = span)
       when is_list(fields) do
    spelling = to_string(field)

    ranked =
      fields
      |> Enum.map(&{to_string(&1), Suggest.distance(spelling, to_string(&1))})
      |> Enum.sort_by(fn {candidate, distance} -> {distance, String.downcase(candidate), candidate} end)

    case ranked do
      [{candidate, distance}, {_other, next_distance} | _]
      when distance <= 2 and distance < next_distance ->
        [
          %Suggestion{
            message: "Replace it with `#{candidate}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: candidate}]
          }
        ]

      [{candidate, distance}] when distance <= 2 ->
        [
          %Suggestion{
            message: "Replace it with `#{candidate}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: candidate}]
          }
        ]

      _ ->
        [
          %Suggestion{
            message: "Use one of: #{Enum.map_join(fields, ", ", &"`#{&1}`")}",
            applicability: :manual
          }
        ]
    end
  end

  defp syntax_family_field_suggestions(_details, _span), do: []

  defp macro_capture_suggestions(%{capture: capture, available_captures: captures}, %Span{} = span)
       when is_list(captures) do
    spelling = to_string(capture)

    ranked =
      captures
      |> Enum.map(&{to_string(&1), Suggest.distance(spelling, to_string(&1))})
      |> Enum.sort_by(fn {candidate, distance} -> {distance, String.downcase(candidate), candidate} end)

    case ranked do
      [{candidate, distance}, {_other, next_distance} | _]
      when distance <= 2 and distance < next_distance ->
        [
          %Suggestion{
            message: "Replace it with the declared capture `#{candidate}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: candidate}]
          }
        ]

      [{candidate, distance}] when distance <= 2 ->
        [
          %Suggestion{
            message: "Replace it with the declared capture `#{candidate}`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: candidate}]
          }
        ]

      _ ->
        [
          %Suggestion{
            message: "Refer to one of this rule's captures: #{Enum.map_join(captures, ", ", &"`#{&1}`")}",
            applicability: :manual
          }
        ]
    end
  end

  defp macro_capture_suggestions(_details, _span), do: []

  defp insertion_before(%Span{} = span) do
    %{
      span
      | end_byte: span.start_byte,
        end_line: span.start_line,
        end_column: span.start_column
    }
  end

  defp insertion_before(_span), do: nil

  defp record_field_candidates(nil, _declared, _record), do: []

  defp record_field_candidates(field, declared, record) do
    candidates =
      Enum.map(declared, fn name ->
        %{
          id: {record, name},
          name: name_to_string(name),
          namespace: :field,
          owner: record,
          visibility: :public,
          imported: true,
          origin: :record_shape
        }
      end)

    Suggest.rank(candidates, name_to_string(field), :field)
  end

  defp record_field_suggestions(field, [%{name: candidate} = first | rest], %Span{} = span) do
    unique? =
      Enum.all?(rest, fn other ->
        Suggest.distance(name_to_string(field), first.name) <
          Suggest.distance(name_to_string(field), other.name)
      end)

    if unique? do
      [
        %Suggestion{
          message: "Replace it with `#{candidate}`",
          applicability: :machine_applicable,
          edits: [%TextEdit{span: span, replacement: candidate}]
        }
      ]
    else
      []
    end
  end

  defp record_field_suggestions(_field, _candidates, _span), do: []

  defp unique_record_field_candidate(field, [%{name: candidate} = first | rest]) when not is_nil(field) do
    distance = Suggest.distance(name_to_string(field), candidate)

    if Enum.all?(rest, &(distance < Suggest.distance(name_to_string(field), &1.name))),
      do: first
  end

  defp unique_record_field_candidate(_field, _candidates), do: nil

  defp record_operation_label(%Span{} = span, primary_span, record, operation) when span != primary_span do
    action =
      if(operation == :record_update,
        do: "this is a `#{surface_declaration_name(record)}` update",
        else: "this constructs `#{surface_declaration_name(record)}`"
      )

    %Label{span: span, style: :secondary, message: action}
  end

  defp record_operation_label(_span, _primary_span, _record, _operation), do: nil

  defp record_update_base_label(%Span{} = span, primary_span, :record_update) when span != primary_span,
    do: %Label{span: span, style: :secondary, message: "unchanged fields come from this value"}

  defp record_update_base_label(_span, _primary_span, _operation), do: nil

  defp missing_record_field_suggestions([]), do: []

  defp missing_record_field_suggestions(fields) do
    [
      %Suggestion{
        message: "Add #{missing_field_label(fields)} before the closing `}`",
        applicability: :manual
      }
    ]
  end

  defp missing_field_label([field]), do: "the missing field `#{name_to_string(field)}`"

  defp missing_field_label(fields) do
    "the missing fields " <> Enum.map_join(fields, ", ", &"`#{name_to_string(&1)}`")
  end

  defp field_list([field]), do: "`#{name_to_string(field)}`"

  defp field_list(fields) do
    fields
    |> Enum.map_join(", ", &"`#{name_to_string(&1)}`")
  end

  defp syntax_problem_code(:unterminated_lambda), do: "E035"
  defp syntax_problem_code(:unrecognized_pattern), do: "E090"
  defp syntax_problem_code(_kind), do: "E094"

  defp syntax_problem_title(%SyntaxProblem{kind: :unterminated_lambda}), do: "Lambda body is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unrecognized_pattern}), do: "Pattern is not supported"
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
  defp syntax_problem_title(%SyntaxProblem{kind: :missing_function_body}), do: "Function body is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :function_parameters_unparenthesized}),
    do: "Function parameter list is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :lambda_parameters_unparenthesized}),
    do: "Lambda parameter list is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :lambda_arrow_missing}), do: "Lambda arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :induction_case}}),
    do: "Induction case arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_using_missing}), do: "Rewrite command needs `using`"
  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_in_missing}), do: "Rewrite expression needs `in`"
  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_occurrence_invalid}), do: "Rewrite occurrence is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :rewrite_hypothesis_name_invalid}),
    do: "Rewrite target needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :induction_case_introducer_missing}),
    do: "Induction branch needs `case`"

  defp syntax_problem_title(%SyntaxProblem{kind: :induction_block_indent_missing}),
    do: "Induction cases must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_check_else_missing}),
    do: "Macro check needs `else`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_check_fail_missing}),
    do: "Macro check needs `fail`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_check_failure_constructor_invalid}),
    do: "Macro check needs a failure value"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_rule_becomes_missing}),
    do: "Macro rule needs `becomes`"

  defp syntax_problem_title(%SyntaxProblem{kind: :literal_rule_becomes_missing}),
    do: "Literal rule needs `becomes`"

  defp syntax_problem_title(%SyntaxProblem{kind: :computed_rule_by_missing}),
    do: "Computed rule needs `by`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_example_expands_missing}),
    do: "Macro example needs `expands`"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_expands_with_missing}),
    do: "Macro expander needs `with`"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_indent_missing}),
    do: "Syntax family body must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_member_invalid}),
    do: "Syntax family member is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_entry_invalid}),
    do: "Structured macro entry is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_production_invalid}),
    do: "Structured macro production is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :syntax_family_body_indent_missing}),
    do: "Structured macro body must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_definition_entry_invalid}),
    do: "Macro declaration entry is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_example_entry_invalid}),
    do: "Macro example entry is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :macro_explain_point_invalid}),
    do: "Macro explanation point is invalid"

  defp syntax_problem_title(%SyntaxProblem{kind: :local_function_keyword_missing}),
    do: "Local function needs `fn`"

  defp syntax_problem_title(%SyntaxProblem{kind: :implementation_for_keyword_missing}),
    do: "Implementation needs `for`"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :explain_clause}}),
    do: "Explanation clause arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :match_arm}}),
    do: "Pattern branch arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: family}})
       when family in [:pickup_clause, :pickup_else],
       do: "Pickup branch arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :function_clause}}),
    do: "Function clause arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: family}})
       when family in [:with_arm, :with_rematch_arm],
       do: "With branch arrow is missing"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_binder_invalid}),
    do: "Refinement binder needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_colon_missing}),
    do: "Refinement binder needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_bar_missing}),
    do: "Refinement type needs a separator"

  defp syntax_problem_title(%SyntaxProblem{kind: :refinement_unclosed}),
    do: "Refinement type is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :refinement_type}}),
    do: "Refinement type has the wrong closer"

  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_binder_invalid}), do: "Sigma binder needs a name"
  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_colon_missing}), do: "Sigma binder needs a colon"
  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_comma_missing}), do: "Sigma type needs a separator"
  defp syntax_problem_title(%SyntaxProblem{kind: :sigma_unclosed}), do: "Sigma type is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :sigma_type}}),
    do: "Sigma type has the wrong closer"

  defp syntax_problem_title(%SyntaxProblem{kind: :gadt_constructor_colon_missing}),
    do: "Constructor signature needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :record_field_colon_missing}),
    do: "Record field needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :fixity_colon_missing}),
    do: "Fixity declaration needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :precedencegroup_field_colon_missing}),
    do: "Precedence group field needs a colon"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :type_declaration_assign_missing,
         context: %{family: :typealias}
       }),
       do: "Type alias needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :type_declaration_assign_missing}),
    do: "Type declaration needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :type_indices_opener_missing}),
    do: "Type indices need parentheses"

  defp syntax_problem_title(%SyntaxProblem{kind: :assert_type_colon_missing}),
    do: "Type assertion needs a colon"

  defp syntax_problem_title(%SyntaxProblem{kind: :named_implicit_pattern_assign_missing}),
    do: "Named implicit pattern needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :local_binding_assign_missing,
         context: %{family: :have}
       }),
       do: "Have binding needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :local_binding_assign_missing}),
    do: "Let binding needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :where_block_indent_missing}),
    do: "Local definitions must be indented"

  defp syntax_problem_title(%SyntaxProblem{kind: :where_binding_assign_missing}),
    do: "Local definition needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true, container: :record}
       }),
       do: "Record fields need a separator"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true}
       }),
       do: "Map entries need a separator"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{container: :record}
       }),
       do: "Record entry needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{kind: :map_entry_separator_missing}),
    do: "Map entry needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{kind: :binary_generator_arrow_missing}),
    do: "Binary generator needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{kind: :send_comma_missing}),
    do: "Send needs a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{annotated: true}
       }),
       do: "Lifted callback needs an equals sign"

  defp syntax_problem_title(%SyntaxProblem{kind: :lift_callback_body_separator_missing}),
    do: "Lifted callback needs an arrow"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: container}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "Macro parameter list is missing"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: :macro_obligation_capture}
       }),
       do: "Macro obligation needs parentheses"

  defp syntax_problem_title(%SyntaxProblem{kind: :with_rematch_separator_missing}),
    do: "With rematch needs a bar"

  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_parameter_name, context: %{lambda: true}}),
    do: "Lambda parameter needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :invalid_parameter_name}), do: "Function parameter needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :variadic_parameter_name_missing}),
    do: "Variadic parameter needs a name"

  defp syntax_problem_title(%SyntaxProblem{kind: :call_unclosed}), do: "Function call is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :call_argument_separator_missing}),
    do: "Call arguments need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :list}}),
    do: "List is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :tuple}}),
    do: "Tuple is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: container}})
       when container in [:tuple_type, :tuple_type_sigil],
       do: "Tuple type is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :grouped_type}}),
    do: "Grouped type is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :grouped_expression}
       }),
       do: "Parenthesized expression is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_constructor_domain}
       }),
       do: "Named constructor domain is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_constructor_domain}
       }),
       do: "Implicit constructor domain is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_implicit_pattern}
       }),
       do: "Named implicit pattern is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_parameter}
       }),
       do: "Implicit parameter is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_specifier_arguments}
       }),
       do: "Binary specifier argument is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :selective_import}
       }),
       do: "Selective import is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :failure_parameters}
       }),
       do: "Failure parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :lift_callback_parameters}
       }),
       do: "Lifted callback parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :macro_obligation_capture}
       }),
       do: "Macro obligation is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container}
       })
       when container in [:splice, :splice_group],
       do: "Syntax splice is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :match}
       }),
       do: "Pattern branch block is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: family}
       })
       when family in [:with, :multi_with],
       do: "With branch block is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :map}}),
    do: "Map is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :record}}),
    do: "Record is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :list_cons}}),
    do: "List cons is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :comprehension}
       }),
       do: "List comprehension is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :parameters}
       }),
       do: "Function parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :type_arguments}
       }),
       do: "Type application is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :type_parameters}
       }),
       do: "Type parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :constructor_parameters}
       }),
       do: "Constructor parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :type_indices}
       }),
       do: "Type index list is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :lambda_parameters}
       }),
       do: "Lambda parameter list is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_unclosed, context: %{container: :binary_literal}}),
    do: "Binary literal is not closed"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_generator}
       }),
       do: "Binary generator is not closed"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: :list}}),
    do: "List elements need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: :tuple}}),
    do: "Tuple elements need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: container}})
       when container in [:tuple_type, :tuple_type_sigil],
       do: "Tuple type positions need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :grouped_type}
       }),
       do: "Grouped type positions need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_separator_missing, context: %{container: :map}}),
    do: "Map entries need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :record}
       }),
       do: "Record fields need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :parameters}
       }),
       do: "Function parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_arguments}
       }),
       do: "Type arguments need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_parameters}
       }),
       do: "Type parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :constructor_parameters}
       }),
       do: "Constructor parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_indices}
       }),
       do: "Type indices need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :lambda_parameters}
       }),
       do: "Lambda parameters need a comma"

  defp syntax_problem_title(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :selective_import}
       }),
       do: "Imported names need a comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_trailing_separator, context: %{container: :list}}),
    do: "List ends with an extra comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :container_trailing_separator, context: %{container: :tuple}}),
    do: "Tuple ends with an extra comma"

  defp syntax_problem_title(%SyntaxProblem{kind: :bare_brace_expression}), do: "Brace cannot start an expression"
  defp syntax_problem_title(%SyntaxProblem{kind: :unmatched_closer}), do: "Closing delimiter has no opener"
  defp syntax_problem_title(%SyntaxProblem{kind: :mismatched_closer}), do: "Closing delimiter does not match"
  defp syntax_problem_title(%SyntaxProblem{kind: :unclosed_parentheses}), do: "Parenthesized expression is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unclosed_brackets}), do: "Bracketed expression is not closed"
  defp syntax_problem_title(%SyntaxProblem{kind: :unclosed_braces}), do: "Braced expression is not closed"
  defp syntax_problem_title(_problem), do: "I got stuck while parsing this"

  defp syntax_problem_context(%SyntaxProblem{
         kind: :unterminated_lambda,
         expected: :rbrace,
         context: %{body_style: :brace}
       }),
       do: "This brace-delimited lambda body reaches the end of its container without the '}' that closes it."

  defp syntax_problem_context(%SyntaxProblem{kind: :unterminated_lambda}),
    do: "This multi-statement lambda body reaches the end of its container without a closing delimiter."

  defp syntax_problem_context(%SyntaxProblem{kind: :unrecognized_pattern, observed: :range}),
    do:
      "A range describes many values, but a pattern must describe a shape Cure can deconstruct. Bind the value and test the range in a guard instead."

  defp syntax_problem_context(%SyntaxProblem{kind: :unrecognized_pattern, observed: observed}),
    do: "#{String.capitalize(syntax_name(observed))} is not a pattern form Cure can deconstruct here."

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
      capitalize_sentence(macro_expectation(expected, observed))
  end

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_literal_capture, expected: expected}),
    do: "This macro capture must match the literal shape `#{syntax_name(expected)}`."

  defp syntax_problem_context(%SyntaxProblem{kind: :non_associative, context: %{operator: operator}}),
    do: "The #{syntax_name(operator)} operator cannot be chained without parentheses."

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

  defp syntax_problem_context(%SyntaxProblem{kind: :missing_function_body}),
    do: "This function declaration ends after `=`, but every function needs a body expression."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :function_parameters_unparenthesized,
         context: %{function: function}
       }),
       do:
         "The function `#{function}` needs a parenthesized parameter list after its name. Write `()` when it takes no parameters."

  defp syntax_problem_context(%SyntaxProblem{kind: :lambda_parameters_unparenthesized}),
    do: "An anonymous function must put its parameters inside parentheses immediately after `fn`."

  defp syntax_problem_context(%SyntaxProblem{kind: :lambda_arrow_missing}),
    do: "A lambda needs `->` between its parameter list and body expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :induction_case}}),
    do: "An induction case needs `=>` between its pattern and body expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_using_missing, observed: observed}),
    do:
      "A directed rewrite introduces its equality proof with `using`; #{authored_syntax(observed)} appears where `using` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_in_missing, observed: observed}),
    do:
      "A rewrite expression uses `in` between its equality proof and the expression being rewritten; #{authored_syntax(observed)} appears where `in` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_occurrence_invalid, observed: observed}),
    do:
      "The selector after `at` must be a positive integer occurrence such as `1`; #{authored_syntax(observed)} cannot select an occurrence."

  defp syntax_problem_context(%SyntaxProblem{kind: :rewrite_hypothesis_name_invalid, observed: observed}),
    do: "The selector after `in` must name a local hypothesis; #{authored_syntax(observed)} is not a hypothesis name."

  defp syntax_problem_context(%SyntaxProblem{kind: :induction_case_introducer_missing, observed: observed}),
    do:
      "Every branch in an induction block starts with `case`; #{authored_syntax(observed)} appears at the start of this branch."

  defp syntax_problem_context(%SyntaxProblem{kind: :induction_block_indent_missing}),
    do: "The `case` branches of an induction expression must form an indented block below its subject."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_check_else_missing, observed: observed}),
    do:
      "A macro check uses `else` between its condition and failure value; #{authored_syntax(observed)} appears where `else` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_check_fail_missing, observed: observed}),
    do:
      "The rejected branch of a macro check starts with `fail`; #{authored_syntax(observed)} appears where `fail` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_check_failure_constructor_invalid, observed: observed}),
    do:
      "After `fail`, write a declared macro failure with its arguments, such as `BadInput(value)`; #{authored_syntax(observed)} is not a failure constructor call."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_rule_becomes_missing, observed: observed}),
    do:
      "A syntax rule uses `becomes` between its matched form and expansion template; #{authored_syntax(observed)} appears where `becomes` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :literal_rule_becomes_missing, observed: observed}),
    do:
      "A literal rule uses `becomes` between its suffix pattern and expansion template; #{authored_syntax(observed)} appears where `becomes` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :computed_rule_by_missing, observed: observed}),
    do:
      "A computed rule uses `by` before the elaborator function that implements it; #{authored_syntax(observed)} appears where `by` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_example_expands_missing, observed: observed}),
    do:
      "A macro example uses `expands` between its use-site and expected result; #{authored_syntax(observed)} appears where `expands` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_expands_with_missing, observed: observed}),
    do:
      "A structured macro uses `expands with` before its expander function; #{authored_syntax(observed)} appears where `with` belongs."

  defp syntax_problem_context(%SyntaxProblem{kind: :syntax_family_indent_missing, context: %{family: family}}),
    do:
      "The fields, included families, and productions of `#{family}` must be nested below its `syntax family` declaration."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_member_invalid,
         observed: observed,
         context: %{family: family}
       }),
       do:
         "#{authored_syntax(observed)} cannot declare a member of the `#{family}` syntax family. Write a typed field, `includes Family`, or a `syntax` production."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_entry_invalid,
         observed: observed,
         context: %{family: family, valid_fields: valid_fields}
       }),
       do:
         "#{authored_syntax(observed)} does not start a field of the `#{family}` structured macro body. Valid fields are #{inline_choices(valid_fields)}."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_production_invalid,
         observed: observed,
         context: context
       }) do
    field = Map.get(context, :field, "this field")
    family = Map.get(context, :family)
    owner = if family, do: " in `#{family}`", else: ""

    "#{authored_syntax(observed)} does not match any production accepted by `#{field}`#{owner}. Follow one of the forms declared by that syntax family."
  end

  defp syntax_problem_context(%SyntaxProblem{
         kind: :syntax_family_body_indent_missing,
         context: %{family: family, valid_fields: valid_fields}
       }),
       do:
         "The `#{family}` structured macro body must be indented below its invocation. Its fields are #{inline_choices(valid_fields)}."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_definition_entry_invalid, observed: observed}),
    do:
      "#{authored_syntax(observed)} cannot start an entry in a macro declaration. Use a syntax rule, family contract, expander, literal rule, explanation, failure, or opened category."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_example_entry_invalid, observed: observed}),
    do:
      "#{authored_syntax(observed)} cannot start a pinned macro example. Each line in this nested block must use `example use_site expands expected`."

  defp syntax_problem_context(%SyntaxProblem{kind: :macro_explain_point_invalid, observed: observed}),
    do:
      "#{authored_syntax(observed)} cannot name a macro failure point. Use a failure category such as `Duration`, or `keyword \"every\"` for a literal token."

  defp syntax_problem_context(%SyntaxProblem{kind: :local_function_keyword_missing}),
    do: "A private function declaration must put `fn` between `local` and the function name."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :implementation_for_keyword_missing,
         context: %{declaration: declaration}
       }),
       do:
         "The implementation of `#{declaration}` needs `for` between its interface or protocol and the type receiving the implementation."

  defp syntax_problem_context(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :explain_clause}}),
    do: "An explanation clause needs `=>` between its failure point and message."

  defp syntax_problem_context(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: family}}),
    do: "#{branch_family_name(family)} needs `->` between its head and body expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_binder_invalid, observed: observed}),
    do:
      "#{String.capitalize(syntax_name(observed))} cannot name the value refined by this type. Use a lower-case name such as `value`."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_colon_missing}),
    do: "A refinement binder must be followed by `:` and the base type whose values it describes."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_bar_missing}),
    do: "A refinement type uses `|` between its base type and the proposition values must satisfy."

  defp syntax_problem_context(%SyntaxProblem{kind: :refinement_unclosed}),
    do: "This refinement type reaches the end of its container without the '}' that closes its proposition."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :mismatched_closer,
         expected: expected,
         observed: observed,
         context: %{family: :refinement_type}
       }),
       do:
         "This refinement type starts with '{', so #{authored_syntax(observed)} cannot close it. Use '#{syntax_insertion(expected)}' after the proposition."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_binder_invalid, observed: observed}),
    do:
      "#{String.capitalize(syntax_name(observed))} cannot name the first value in this dependent pair. Use a lower-case binder such as `value`."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_colon_missing}),
    do: "A Sigma binder must be followed by `:` and the type of its first value."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_comma_missing}),
    do: "A Sigma type uses `,` between the first value's type and the dependent type of its second value."

  defp syntax_problem_context(%SyntaxProblem{kind: :sigma_unclosed}),
    do: "This Sigma type reaches the end of the source without the ')' that closes its dependent pair."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :mismatched_closer,
         expected: expected,
         observed: observed,
         context: %{family: :sigma_type}
       }),
       do:
         "This Sigma type starts with '(', so #{authored_syntax(observed)} cannot close it. Use '#{syntax_insertion(expected)}' after the dependent result type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :gadt_constructor_colon_missing,
         context: %{declaration: constructor, family: family}
       }),
       do: "The constructor `#{constructor}` in `#{family}` needs `:` between its name and type signature."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :record_field_colon_missing,
         context: %{declaration: field, family: record}
       }),
       do: "The field `#{field}` in record `#{record}` needs `:` between its name and declared type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :fixity_colon_missing,
         context: %{declaration: operator, family: fixity}
       }),
       do: "The `#{fixity}` declaration for `#{operator}` needs `:` between the operator and its precedence group."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :precedencegroup_field_colon_missing,
         context: %{declaration: field, family: group}
       }),
       do: "The `#{field}` setting in precedence group `#{group}` needs `:` before its value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :type_declaration_assign_missing,
         context: %{declaration: name, family: :typealias}
       }),
       do: "The type alias `#{name}` needs `=` between its name and the type it expands to."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :type_declaration_assign_missing,
         context: %{declaration: name}
       }),
       do: "The type `#{name}` needs `=` between its declaration head and its constructors or aliased type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :type_indices_opener_missing,
         context: %{declaration: declaration}
       }),
       do: "The indexed type `#{declaration}` must put its index telescope inside parentheses after `indices`."

  defp syntax_problem_context(%SyntaxProblem{kind: :assert_type_colon_missing}),
    do: "The `assert_type` expression needs `:` between the asserted value and its expected type."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :named_implicit_pattern_assign_missing,
         context: %{binder: binder}
       }),
       do: "The named implicit pattern for `#{binder}` needs `=` before the pattern that fixes its value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :local_binding_assign_missing,
         context: %{family: family, declaration: name}
       }),
       do: "The `#{family}` binding for `#{name}` needs `=` before the value it binds."

  defp syntax_problem_context(%SyntaxProblem{kind: :where_block_indent_missing}),
    do: "Definitions belonging to this `where` block must be indented beneath it."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :where_binding_assign_missing,
         context: %{declaration: name}
       }),
       do: "The local definition `#{name}` needs `=` between its name and value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true, container: container, key: key}
       }),
       do:
         "After `#{key}`, this could be another punned #{container} entry needing `,`, or the value of `#{key}` needing `=>`."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{container: :record}
       }),
       do: "This explicit record entry needs `=>` between its key and value."

  defp syntax_problem_context(%SyntaxProblem{kind: :map_entry_separator_missing}),
    do: "This explicit map entry needs `=>` between its key and value."

  defp syntax_problem_context(%SyntaxProblem{kind: :binary_generator_arrow_missing}),
    do: "This binary generator needs `<-` between its byte pattern and source expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :send_comma_missing}),
    do: "The keyword `send` form needs `,` between its target and message."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{declaration: name, annotated: true}
       }),
       do: "The lifted callback `#{name}` needs `=` between its declared return type and body."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{declaration: name}
       }),
       do: "The lifted callback `#{name}` needs `->` between its parameter list and body."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: container, declaration: declaration}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "The macro declaration `#{declaration}` must put its parameters inside parentheses."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: :macro_obligation_capture, interface: interface}
       }),
       do: "The `#{interface}` obligation must put the capture it constrains inside parentheses."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :with_rematch_separator_missing,
         context: %{parent_pattern_count: count}
       }),
       do: "These #{count} restated parent patterns need `|` before the pattern for the `with` value."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :invalid_parameter_name,
         observed: observed,
         context: %{lambda: true}
       }),
       do:
         "#{String.capitalize(syntax_name(observed))} cannot name a lambda parameter. Use a lower-case name such as `value`."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :invalid_parameter_name,
         observed: observed,
         context: %{implicit: true}
       }),
       do:
         "#{String.capitalize(syntax_name(observed))} cannot name an implicit parameter. Write a lower-case binder such as `{type}` or `{type: Type}`."

  defp syntax_problem_context(%SyntaxProblem{kind: :invalid_parameter_name, observed: observed}),
    do:
      "#{String.capitalize(syntax_name(observed))} cannot name a function parameter. Use a lower-case name such as `value`, optionally followed by `: Type`."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :variadic_parameter_name_missing,
         context: %{kind: :keyword_variadic}
       }),
       do: "The `**` marker must be followed by the name that receives extra named arguments, for example `**options`."

  defp syntax_problem_context(%SyntaxProblem{kind: :variadic_parameter_name_missing}),
    do: "The `*` marker must be followed by the name that receives extra positional arguments, for example `*values`."

  defp syntax_problem_context(%SyntaxProblem{kind: :call_unclosed, context: %{call: call}}),
    do: "The call to `#{call}` reaches the end of the source without the ')' that closes its argument list."

  defp syntax_problem_context(%SyntaxProblem{kind: :call_argument_separator_missing, context: %{call: call}}),
    do: "The call to `#{call}` has another argument here, but consecutive arguments must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbrace,
         context: %{container: :map}
       }),
       do: "This map reaches the end of the source without the '}' that closes its entries."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbrace,
         context: %{container: :record}
       }),
       do: "This record reaches the end of the source without the '}' that closes its fields."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbracket,
         context: %{container: :list_cons}
       }),
       do: "This list cons reaches the end of the source without the ']' after its tail expression."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rbracket,
         context: %{container: :comprehension}
       }),
       do: "This list comprehension reaches the end of the source without the ']' that closes its clauses."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :parameters}
       }),
       do: "This function's parameter list reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_arguments, type: type, token_type: :dedent}
       }),
       do: "The type application `#{type}` ends before the ')' that closes its arguments."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_arguments, type: type}
       }),
       do: "The type application `#{type}` reaches the end of the source without the ')' that closes its arguments."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_parameters, declaration: declaration}
       }),
       do: "The declaration of `#{declaration}` reaches the end of its type parameter list without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :constructor_parameters, constructor: constructor}
       }),
       do: "The constructor `#{constructor}` reaches the end of its parameter list without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_indices, declaration: declaration}
       }),
       do: "The indexed type `#{declaration}` reaches the end of its index telescope without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :lambda_parameters}
       }),
       do: "This lambda's parameter list reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: expected,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil] and expected in [:rparen, :rbracket],
       do:
         "This tuple type reaches the end of the source without the '#{syntax_insertion(expected)}' that closes its positions."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :grouped_type}
       }),
       do: "This grouped type reaches the end of the source without the ')' that closes its positions."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :grouped_expression}
       }),
       do: "This parenthesized expression reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_constructor_domain}
       }),
       do: "This named constructor domain reaches the end of the declaration without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_constructor_domain}
       }),
       do: "This implicit constructor domain reaches the end of the declaration without its closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_implicit_pattern, binder: binder}
       }),
       do: "The named implicit pattern for `#{binder}` reaches the end of its value without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_parameter, binder: binder}
       }),
       do: "The implicit parameter `#{binder}` reaches the end of its annotation without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_specifier_arguments, specifier: specifier}
       }),
       do: "The binary `#{specifier}` specifier reaches the end of its argument without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :selective_import, module: module}
       }),
       do: "The selective import from `#{module}` reaches the end of its names without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container, declaration: declaration}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "The parameter list for `#{declaration}` reaches its body without the closing ')'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :macro_obligation_capture, interface: interface, capture: capture}
       }),
       do: "The `#{interface}` obligation for `#{capture}` is missing the ')' that closes its capture."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container}
       })
       when container in [:splice, :splice_group] do
    form = if container == :splice_group, do: "group splice", else: "splice"
    "This #{form} reaches the end of its expression without the closing ')'."
  end

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :match}
       }),
       do: "This inline `match` reaches the end of its branches without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :with}
       }),
       do: "This inline `with` reaches the end of its branches without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block, family: :multi_with}
       }),
       do: "This multi-scrutinee `with` reaches the end of its branches without the closing '}'."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_literal}
       }),
       do: "This binary literal reaches the end of the source without the '>>' that closes its segments."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_generator}
       }),
       do: "This binary generator reaches the end of the source without the '>>' after its source expression."

  defp syntax_problem_context(%SyntaxProblem{kind: :container_unclosed, context: %{container: container}}),
    do: "This #{container} reaches the end of the source without the ']' that closes its elements."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :map}
       }),
       do: "This map has another entry here, but consecutive entries must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :record}
       }),
       do: "This record has another field here, but consecutive fields must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :parameters}
       }),
       do: "This function has another parameter here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_arguments, type: type}
       }),
       do:
         "The type application `#{type}` has another argument here, but consecutive type arguments must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_parameters, declaration: declaration}
       }),
       do:
         "The declaration of `#{declaration}` has another type parameter here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :constructor_parameters, constructor: constructor}
       }),
       do:
         "The constructor `#{constructor}` has another parameter type here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_indices, declaration: declaration}
       }),
       do:
         "The indexed type `#{declaration}` has another index here, but consecutive indices must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :lambda_parameters}
       }),
       do: "This lambda has another parameter here, but consecutive parameters must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :selective_import, module: module}
       }),
       do: "The import from `#{module}` has another name here, but imported names must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
       do: "This type has another position here, but consecutive type positions must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: container}
       }),
       do: "This #{container} has another element here, but consecutive elements must be separated by a comma."

  defp syntax_problem_context(%SyntaxProblem{
         kind: :container_trailing_separator,
         context: %{container: container}
       }),
       do: "This #{container} ends immediately after a comma, but every comma must be followed by another element."

  defp syntax_problem_context(%SyntaxProblem{kind: :bare_brace_expression}),
    do:
      "A bare '{' does not begin a Cure expression. Write `Type{...}` for a record, `\#{...}` for a map, or use indentation for a block."

  defp syntax_problem_context(%SyntaxProblem{kind: :unmatched_closer, observed: observed}),
    do: "#{syntax_name(observed)} closes a construct, but there is no matching opener here."

  defp syntax_problem_context(%SyntaxProblem{kind: :mismatched_closer, expected: expected, observed: observed}),
    do: "This construct needs #{syntax_name(expected)}, but it is closed with #{syntax_name(observed)} instead."

  defp syntax_problem_context(%SyntaxProblem{kind: :unclosed_parentheses}),
    do: "This parenthesized expression reaches the end of the source without its closing ')'."

  defp syntax_problem_context(%SyntaxProblem{kind: :unclosed_brackets}),
    do: "This bracketed expression reaches the end of the source without its closing ']'."

  defp syntax_problem_context(%SyntaxProblem{kind: :unclosed_braces}),
    do: "This braced expression reaches the end of the source without its closing '}'."

  defp syntax_problem_context(%SyntaxProblem{observed: :eof}),
    do: "The source ended while I was still parsing this construct."

  defp syntax_problem_context(%SyntaxProblem{observed: observed}),
    do: "#{String.capitalize(syntax_name(observed))} cannot appear at this point in the construct."

  defp capitalize_sentence(<<first::utf8, rest::binary>>), do: String.upcase(<<first::utf8>>) <> rest
  defp capitalize_sentence(text), do: text

  defp syntax_expected_doc(%SyntaxProblem{expected: nil, alternatives: []}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :macro_use_mismatch}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :mismatched_closer}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :function_parameters_unparenthesized}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :invalid_parameter_name}), do: Doc.empty()
  defp syntax_expected_doc(%SyntaxProblem{kind: :variadic_parameter_name_missing}), do: Doc.empty()

  defp syntax_expected_doc(%SyntaxProblem{kind: kind})
       when kind in [:call_unclosed, :call_argument_separator_missing],
       do: Doc.empty()

  defp syntax_expected_doc(%SyntaxProblem{kind: kind})
       when kind in [:container_unclosed, :container_separator_missing, :container_trailing_separator],
       do: Doc.empty()

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

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_lambda, expected: :rbrace}),
    do: "close this lambda body with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_lambda}), do: "the unclosed body reaches here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unrecognized_pattern, observed: :range}),
    do: "a range operator cannot be used in a pattern"

  defp syntax_problem_label(%SyntaxProblem{kind: :unrecognized_pattern}), do: "this pattern form is not supported"
  defp syntax_problem_label(%SyntaxProblem{kind: :missing_function_body}), do: "write the function body after this `=`"

  defp syntax_problem_label(%SyntaxProblem{kind: :function_parameters_unparenthesized}),
    do: "the parameter list belongs before this token"

  defp syntax_problem_label(%SyntaxProblem{kind: :lambda_parameters_unparenthesized}),
    do: "insert `(` before the first parameter"

  defp syntax_problem_label(%SyntaxProblem{kind: :lambda_arrow_missing}),
    do: "insert `->` before the lambda body"

  defp syntax_problem_label(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :induction_case}}),
    do: "insert `=>` before this induction case body"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_using_missing}),
    do: "insert `using` before the equality proof"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_in_missing}),
    do: "insert `in` before the expression to rewrite"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_occurrence_invalid}),
    do: "write a positive occurrence number here"

  defp syntax_problem_label(%SyntaxProblem{kind: :rewrite_hypothesis_name_invalid}),
    do: "write the local hypothesis name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :induction_case_introducer_missing}),
    do: "this induction branch must start with `case`"

  defp syntax_problem_label(%SyntaxProblem{kind: :induction_block_indent_missing}),
    do: "indent the induction cases below the subject"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_check_else_missing}),
    do: "insert `else` before the rejected branch"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_check_fail_missing}),
    do: "insert `fail` before this failure value"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_check_failure_constructor_invalid}),
    do: "call a declared macro failure here"

  defp syntax_problem_label(%SyntaxProblem{kind: kind, expected: expected, context: %{token_type: type}})
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] and type in [:eof, :dedent, :newline],
       do: "add `#{expected}` and the expression that follows it"

  defp syntax_problem_label(%SyntaxProblem{kind: kind, expected: expected})
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ],
       do: "insert `#{expected}` before this expression"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_indent_missing}),
    do: "indent the syntax family members below this declaration"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_member_invalid}),
    do: "write a field, include, or production here"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_entry_invalid}),
    do: "start this entry with a valid structured field"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_production_invalid}),
    do: "this does not match a declared family production"

  defp syntax_problem_label(%SyntaxProblem{kind: :syntax_family_body_indent_missing}),
    do: "indent the structured macro body here"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_definition_entry_invalid}),
    do: "replace this with a valid macro declaration entry"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_example_entry_invalid}),
    do: "start this line with `example`"

  defp syntax_problem_label(%SyntaxProblem{kind: :macro_explain_point_invalid}),
    do: "name the failure point before `=>`"

  defp syntax_problem_label(%SyntaxProblem{kind: :local_function_keyword_missing}),
    do: "insert `fn` before this function name"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :implementation_for_keyword_missing,
         context: %{repair: :replace}
       }),
       do: "replace this with `for`"

  defp syntax_problem_label(%SyntaxProblem{kind: :implementation_for_keyword_missing}),
    do: "insert `for` before this implementation type"

  defp syntax_problem_label(%SyntaxProblem{kind: :branch_arrow_missing, context: %{family: :explain_clause}}),
    do: "insert `=>` before this explanation message"

  defp syntax_problem_label(%SyntaxProblem{kind: :branch_arrow_missing}),
    do: "insert `->` before this branch body"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_binder_invalid}),
    do: "write a lower-case refinement binder here"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_colon_missing}),
    do: "insert `:` before the base type"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_bar_missing}),
    do: "insert `|` before the proposition"

  defp syntax_problem_label(%SyntaxProblem{kind: :refinement_unclosed}),
    do: "close this refinement type with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :refinement_type}}),
    do: "replace this with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_binder_invalid}),
    do: "write a lower-case Sigma binder here"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_colon_missing}),
    do: "insert `:` before the first value's type"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_comma_missing}),
    do: "insert `,` before the dependent result type"

  defp syntax_problem_label(%SyntaxProblem{kind: :sigma_unclosed}),
    do: "close this Sigma type with `)`"

  defp syntax_problem_label(%SyntaxProblem{kind: :mismatched_closer, context: %{family: :sigma_type}}),
    do: "replace this with `)`"

  defp syntax_problem_label(%SyntaxProblem{kind: :gadt_constructor_colon_missing}),
    do: "insert `:` before this constructor signature"

  defp syntax_problem_label(%SyntaxProblem{kind: :record_field_colon_missing}),
    do: "insert `:` before this field type"

  defp syntax_problem_label(%SyntaxProblem{kind: :fixity_colon_missing}),
    do: "insert `:` before this precedence group"

  defp syntax_problem_label(%SyntaxProblem{kind: :precedencegroup_field_colon_missing}),
    do: "insert `:` before this setting value"

  defp syntax_problem_label(%SyntaxProblem{kind: :type_declaration_assign_missing}),
    do: "insert `=` before this type body"

  defp syntax_problem_label(%SyntaxProblem{kind: :type_indices_opener_missing}),
    do: "insert `(` before the first type index"

  defp syntax_problem_label(%SyntaxProblem{kind: :assert_type_colon_missing}),
    do: "insert `:` before this expected type"

  defp syntax_problem_label(%SyntaxProblem{kind: :named_implicit_pattern_assign_missing}),
    do: "insert `=` before this implicit pattern"

  defp syntax_problem_label(%SyntaxProblem{kind: :local_binding_assign_missing}),
    do: "insert `=` before this binding value"

  defp syntax_problem_label(%SyntaxProblem{kind: :where_block_indent_missing}),
    do: "indent this definition beneath `where`"

  defp syntax_problem_label(%SyntaxProblem{kind: :where_binding_assign_missing}),
    do: "insert `=` before this local value"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{ambiguous: true}
       }),
       do: "separate these entries with `,`, or make this the value with `=>`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :map_entry_separator_missing,
         context: %{container: :record}
       }),
       do: "insert `=>` before this record value"

  defp syntax_problem_label(%SyntaxProblem{kind: :map_entry_separator_missing}),
    do: "insert `=>` before this map value"

  defp syntax_problem_label(%SyntaxProblem{kind: :binary_generator_arrow_missing}),
    do: "insert `<-` before this generator source"

  defp syntax_problem_label(%SyntaxProblem{kind: :send_comma_missing}),
    do: "insert a comma before this message"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :lift_callback_body_separator_missing,
         context: %{annotated: true}
       }),
       do: "insert `=` before this callback body"

  defp syntax_problem_label(%SyntaxProblem{kind: :lift_callback_body_separator_missing}),
    do: "insert `->` before this callback body"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: container}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "open this parameter list with `(`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_opener_missing,
         context: %{container: :macro_obligation_capture}
       }),
       do: "insert `(` before this capture"

  defp syntax_problem_label(%SyntaxProblem{kind: :with_rematch_separator_missing}),
    do: "insert `|` before this with-pattern"

  defp syntax_problem_label(%SyntaxProblem{kind: :invalid_parameter_name, context: %{lambda: true}}),
    do: "write a lambda parameter name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :invalid_parameter_name}),
    do: "write a parameter name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :variadic_parameter_name_missing}),
    do: "write the variadic parameter name here"

  defp syntax_problem_label(%SyntaxProblem{kind: :call_unclosed}), do: "close this call with `)`"

  defp syntax_problem_label(%SyntaxProblem{kind: :call_argument_separator_missing}),
    do: "insert a comma before this argument"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :parameters}
       }),
       do: "close this parameter list with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_arguments}
       }),
       do: "close these type arguments with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_parameters}
       }),
       do: "close these type parameters with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :constructor_parameters}
       }),
       do: "close this constructor's parameters with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :type_indices}
       }),
       do: "close these type indices with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :lambda_parameters}
       }),
       do: "close this lambda parameter list with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: container}
       })
       when container in [:failure_parameters, :lift_callback_parameters],
       do: "close this macro parameter list with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :rparen,
         context: %{container: :macro_obligation_capture}
       }),
       do: "close this obligation with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_literal}
       }),
       do: "close this binary literal with `>>`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: :binary_close,
         context: %{container: :binary_generator}
       }),
       do: "close this binary generator with `>>`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         expected: expected,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil],
       do: "close this tuple type with `#{syntax_insertion(expected)}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :grouped_type}
       }),
       do: "close this grouped type with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :grouped_expression}
       }),
       do: "close this parenthesized expression with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_constructor_domain}
       }),
       do: "close this named constructor domain with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_constructor_domain}
       }),
       do: "close this implicit constructor domain with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :named_implicit_pattern}
       }),
       do: "close this named implicit pattern with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :implicit_parameter}
       }),
       do: "close this implicit parameter with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :binary_specifier_arguments}
       }),
       do: "close this binary specifier with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :selective_import}
       }),
       do: "close these imported names with `}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: container}
       })
       when container in [:splice, :splice_group],
       do: "close this syntax splice with `)`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_unclosed,
         context: %{container: :branch_block}
       }),
       do: "close this branch block with `}`"

  defp syntax_problem_label(%SyntaxProblem{kind: :container_unclosed, expected: expected}),
    do: "close this container with `#{syntax_insertion(expected)}`"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :map}
       }),
       do: "insert a comma before this entry"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :record}
       }),
       do: "insert a comma before this field"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :parameters}
       }),
       do: "insert a comma before this parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_arguments}
       }),
       do: "insert a comma before this type argument"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_parameters}
       }),
       do: "insert a comma before this type parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :constructor_parameters}
       }),
       do: "insert a comma before this constructor parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :type_indices}
       }),
       do: "insert a comma before this type index"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :lambda_parameters}
       }),
       do: "insert a comma before this lambda parameter"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: :selective_import}
       }),
       do: "insert a comma before this imported name"

  defp syntax_problem_label(%SyntaxProblem{
         kind: :container_separator_missing,
         context: %{container: container}
       })
       when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
       do: "insert a comma before this type position"

  defp syntax_problem_label(%SyntaxProblem{kind: :container_separator_missing}),
    do: "insert a comma before this element"

  defp syntax_problem_label(%SyntaxProblem{kind: :container_trailing_separator}),
    do: "this comma has no following element"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_string}),
    do: "insert the closing `\"` here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_char}),
    do: "insert the closing `'` here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_quoted_identifier}),
    do: "insert the closing backtick here"

  defp syntax_problem_label(%SyntaxProblem{kind: :bare_brace_expression}),
    do: "choose record, map, or block syntax here"

  defp syntax_problem_label(%SyntaxProblem{kind: :unmatched_closer}), do: "this delimiter has nothing to close"
  defp syntax_problem_label(%SyntaxProblem{kind: :mismatched_closer}), do: "replace this mismatched delimiter"

  defp syntax_problem_label(%SyntaxProblem{kind: kind})
       when kind in [:unclosed_parentheses, :unclosed_brackets, :unclosed_braces],
       do: "the closing delimiter belongs here"

  defp syntax_problem_label(%SyntaxProblem{kind: :non_associative}),
    do: "this second operator makes the chain ambiguous"

  defp syntax_problem_label(%SyntaxProblem{kind: :ambiguous_precedence}),
    do: "this operator has no precedence relative to the surrounding one"

  defp syntax_problem_label(_problem), do: "this syntax does not fit here"

  defp computed_macro_content(keyword, :no_compatible_macro_input) do
    {
      "Computed macro expander does not accept its input",
      "The `#{keyword}` macro's expander cannot be applied to any supported reflection of this invocation. Its parameter type must accept the macro's generated syntax record, its direct captured fields, or generic `Syntax`.",
      "this invocation cannot be passed to its expander",
      "The invocation is authored source; change the expander's input type or the macro rule that constructs it."
    }
  end

  defp computed_macro_content(keyword, :normalization_fuel_exhausted) do
    {
      "Computed macro expansion did not terminate",
      "The `#{keyword}` macro's expander exceeded the compiler's bounded evaluation budget before producing syntax. This usually means the expander recurses without reaching a smaller input or performs unexpectedly large compile-time work.",
      "this invocation exhausted the expansion budget",
      "The compiler stopped evaluation safely; no partial generated syntax was accepted."
    }
  end

  defp computed_macro_content(keyword, reason) do
    {
      "Computed macro expansion failed",
      "The `#{keyword}` computed macro could not produce valid Cure syntax: #{computed_macro_reason(reason)}",
      "this macro invocation generated the failing syntax",
      "Edit the authored macro invocation or its rule; generated syntax is not the user-facing source."
    }
  end

  defp computed_macro_payload(:no_compatible_macro_input), do: %{kind: :incompatible_input}
  defp computed_macro_payload(:normalization_fuel_exhausted), do: %{kind: :evaluation_budget_exhausted}

  defp computed_macro_payload({:author_failure, name, _args}),
    do: %{kind: :author_failure, name: name}

  defp computed_macro_payload({:author_diagnostics, diagnostics}),
    do: %{kind: :author_diagnostics, names: author_diagnostic_names(diagnostics)}

  defp computed_macro_payload({:invalid_generated_syntax, {kind, path}}),
    do: %{kind: :invalid_generated_syntax, syntax_problem: kind, path: path}

  defp computed_macro_payload({:host_exception, exception}),
    do: %{kind: :host_exception, exception: exception}

  defp computed_macro_payload(reason), do: %{kind: :expansion_rejected, category: computed_macro_category(reason)}

  defp computed_macro_category(reason) when is_atom(reason), do: reason
  defp computed_macro_category(reason) when is_tuple(reason) and tuple_size(reason) > 0, do: elem(reason, 0)
  defp computed_macro_category(_reason), do: :unknown

  defp computed_macro_reason({:invalid_generated_syntax, {:raw_syntax_in_expansion, path}}),
    do:
      "invalid macro expansion: raw syntax is only valid for reflection, not generated Cure code at #{syntax_path_phrase(path)}"

  defp computed_macro_reason({:invalid_generated_syntax, {:quoted_syntax_in_expansion, path}}),
    do:
      "invalid macro expansion: quoted syntax must be unquoted before it is emitted as Cure code at #{syntax_path_phrase(path)}"

  defp computed_macro_reason({:invalid_generated_syntax, {kind, path}}) do
    {_title, message, _label, _hint} = macro_syntax_integrity_content(kind, path)
    "invalid macro expansion: #{String.downcase(message)}"
  end

  defp computed_macro_reason({:author_diagnostics, diagnostics}) when is_list(diagnostics),
    do: "macro rejected expansion: #{author_diagnostic_summary(diagnostics)}"

  defp computed_macro_reason({:author_failure, name, args}) when is_list(args),
    do: "macro rejected expansion: the macro reported `#{name}`"

  defp computed_macro_reason(_reason), do: "the generated expansion was rejected by the compiler"

  defp computed_macro_suggestions({:invalid_generated_syntax, {:raw_syntax_in_expansion, _path}}),
    do: [
      %Suggestion{
        message: "Return structured `Syntax`; use raw syntax only for reflection",
        applicability: :manual
      }
    ]

  defp computed_macro_suggestions({:invalid_generated_syntax, {:quoted_syntax_in_expansion, _path}}),
    do: [
      %Suggestion{
        message: "Unquote the generated syntax before returning it from the expander",
        applicability: :manual
      }
    ]

  defp computed_macro_suggestions({:invalid_generated_syntax, {kind, path}}) do
    {_title, _message, _label, hint} = macro_syntax_integrity_content(kind, path)
    [%Suggestion{message: hint, applicability: :manual}]
  end

  defp computed_macro_suggestions({:author_diagnostics, diagnostics}),
    do: [
      %Suggestion{
        message: "Address #{author_diagnostic_hint(diagnostics)} at this invocation",
        applicability: :manual
      }
    ]

  defp computed_macro_suggestions({:author_failure, name, _args}),
    do: [%Suggestion{message: "Fix the `#{name}` condition reported by this macro", applicability: :manual}]

  defp computed_macro_suggestions(:no_compatible_macro_input),
    do: [
      %Suggestion{
        message: "Make the expander accept its generated syntax record, captured fields, or generic `Syntax`",
        applicability: :manual
      }
    ]

  defp computed_macro_suggestions(:normalization_fuel_exhausted),
    do: [
      %Suggestion{
        message:
          "Make recursive expansion calls structurally smaller, or move large work out of compile-time evaluation",
        applicability: :manual
      }
    ]

  defp computed_macro_suggestions(_reason),
    do: [%Suggestion{message: "Fix this invocation or the computed macro's expander", applicability: :manual}]

  defp author_diagnostic_summary(diagnostics) do
    case author_diagnostic_names(diagnostics) do
      [] -> "it reported #{length(diagnostics)} authored diagnostic(s)"
      [name] -> "it reported `#{name}`"
      names -> "it reported #{Enum.map_join(names, ", ", &"`#{&1}`")}"
    end
  end

  defp author_diagnostic_hint(diagnostics) do
    case author_diagnostic_names(diagnostics) do
      [] -> "the macro's authored diagnostics"
      [name] -> "the macro's `#{name}` diagnostic"
      names -> "the macro diagnostics #{Enum.map_join(names, ", ", &"`#{&1}`")}"
    end
  end

  defp author_diagnostic_names(diagnostics) do
    diagnostics
    |> Enum.flat_map(fn
      {:macro_failure, name, _args} -> [name_to_string(name)]
      _diagnostic -> []
    end)
    |> Enum.uniq()
  end

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
      {:failure_arguments} -> "failure arguments"
      {:raw_literal} -> "raw literal"
      {:quoted_syntax} -> "quoted syntax"
      other -> inspect(other)
    end)
  end

  defp syntax_secondary_labels(%SyntaxProblem{kind: :macro_use_mismatch} = problem, primary_span) do
    [
      pickup_label(problem.opener, :secondary, "this macro invocation starts here"),
      pickup_label(problem.within, :secondary, "the matching rule is declared here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :mismatched_closer,
           opener: opener,
           previous: previous,
           context: %{family: family, binder_span: binder_span}
         },
         primary_span
       )
       when family in [:refinement_type, :sigma_type] do
    {opener_message, binder_message, previous_message} =
      case family do
        :refinement_type ->
          {"this refinement type starts here", "this is the refinement binder", "the proposition ends here"}

        :sigma_type ->
          {"this Sigma type starts here", "this is the Sigma binder", "the dependent result type ends here"}
      end

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(binder_span, :secondary, binder_message),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: opener,
           previous: previous,
           context: %{container: :macro_obligation_capture} = context
         },
         primary_span
       )
       when kind in [:container_opener_missing, :container_unclosed] do
    open_label =
      if kind == :container_unclosed do
        pickup_label(opener, :secondary, "the capture starts here")
      end

    [
      pickup_label(Map.get(context, :owner_span), :secondary, "this obligation starts here"),
      pickup_label(Map.get(context, :interface_span) || previous, :secondary, "this is the required interface"),
      open_label,
      pickup_label(previous, :secondary, "the capture ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :unterminated_lambda,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    opener_message =
      if Map.get(context, :body_style) == :brace,
        do: "this lambda body starts here",
        else: "this lambda starts here"

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, "the previous body expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :variadic_parameter_name_missing, opener: %Span{} = marker},
         primary_span
       )
       when marker != primary_span,
       do: [%Label{span: marker, style: :secondary, message: "this variadic marker needs a binder"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :lambda_parameters_unparenthesized, opener: %Span{} = lambda},
         primary_span
       )
       when lambda != primary_span,
       do: [%Label{span: lambda, style: :secondary, message: "this lambda starts here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :lambda_arrow_missing,
           opener: %Span{} = lambda,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(lambda, :secondary, "this lambda starts here"),
      pickup_label(previous, :secondary, "its parameter list ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: %{family: :induction_case}
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this induction case starts here"),
      pickup_label(previous, :secondary, "the induction pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [
              :rewrite_using_missing,
              :rewrite_in_missing,
              :rewrite_occurrence_invalid,
              :rewrite_hypothesis_name_invalid
            ] do
    previous_message =
      case kind do
        :rewrite_using_missing -> "the rewrite direction ends here"
        :rewrite_in_missing -> "the equality proof ends here"
        :rewrite_occurrence_invalid -> "this `at` selector needs an occurrence number"
        :rewrite_hypothesis_name_invalid -> "this `in` selector needs a hypothesis name"
      end

    [
      pickup_label(opener, :secondary, "this rewrite command starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous, context: context},
         primary_span
       )
       when kind in [:syntax_family_indent_missing, :syntax_family_member_invalid] do
    previous_message =
      case kind do
        :syntax_family_indent_missing ->
          "the syntax family header ends here"

        :syntax_family_member_invalid ->
          if previous == Map.get(context, :name_span),
            do: "the syntax family header ends here",
            else: "the previous family member ends here"
      end

    [
      pickup_label(opener, :secondary, "this syntax family declaration starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, previous: %Span{} = previous},
         primary_span
       )
       when kind in [:syntax_family_entry_invalid, :syntax_family_production_invalid] and
              previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "the previous structured entry ends here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :macro_definition_entry_invalid,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    previous_message =
      if previous && previous.start_line == opener.start_line,
        do: "the macro header ends here",
        else: "the previous macro entry ends here"

    [
      pickup_label(opener, :secondary, "this macro declaration starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [:macro_example_entry_invalid, :macro_explain_point_invalid] do
    {opener_message, previous_message} =
      case kind do
        :macro_example_entry_invalid ->
          {"this syntax rule owns the example block", "the previous macro example ends here"}

        :macro_explain_point_invalid ->
          {"this explanation block starts here", "the previous explanation clause ends here"}
      end

    [pickup_label(opener, :secondary, opener_message), pickup_label(previous, :secondary, previous_message)]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] do
    {opener_message, previous_message} =
      case kind do
        :macro_rule_becomes_missing -> {"this syntax rule starts here", "the matched form ends here"}
        :literal_rule_becomes_missing -> {"this literal rule starts here", "the suffix pattern ends here"}
        :computed_rule_by_missing -> {"this computed rule starts here", "the computed modifier ends here"}
        :macro_example_expands_missing -> {"this macro example starts here", "the example use-site ends here"}
        :macro_expands_with_missing -> {"this expander section starts here", "the `expands` keyword ends here"}
      end

    [pickup_label(opener, :secondary, opener_message), pickup_label(previous, :secondary, previous_message)]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :induction_case_introducer_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this induction block starts here"),
      pickup_label(previous, :secondary, "the previous induction case ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :induction_block_indent_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this induction expression starts here"),
      pickup_label(previous, :secondary, "the induction subject ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: kind, opener: %Span{} = opener, previous: previous},
         primary_span
       )
       when kind in [
              :macro_check_else_missing,
              :macro_check_fail_missing,
              :macro_check_failure_constructor_invalid
            ] do
    previous_message =
      case kind do
        :macro_check_else_missing -> "the checked condition ends here"
        :macro_check_fail_missing -> "the rejected branch starts after this `else`"
        :macro_check_failure_constructor_invalid -> "this `fail` needs a failure constructor call"
      end

    [
      pickup_label(opener, :secondary, "this macro check starts here"),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: %{family: :explain_clause}
         },
         primary_span
       ) do
    labels =
      if opener == previous do
        [pickup_label(previous, :secondary, "this is the failure point")]
      else
        [
          pickup_label(opener, :secondary, "this explanation clause starts here"),
          pickup_label(previous, :secondary, "the failure point ends here")
        ]
      end

    labels
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :branch_arrow_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "this branch head ends here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :gadt_constructor_colon_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "this is the constructor name"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :type_indices_opener_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "the index telescope follows this keyword"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :assert_type_colon_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this type assertion starts here"),
      pickup_label(previous, :secondary, "the asserted expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :named_implicit_pattern_assign_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this named implicit pattern starts here"),
      pickup_label(previous, :secondary, "this is the implicit binder")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :local_binding_assign_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this #{Map.get(context, :family, :let)} binding starts here"),
      pickup_label(Map.get(context, :pattern_span), :secondary, "this is the binding pattern"),
      pickup_label(previous, :secondary, "the binding head ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :where_block_indent_missing,
           opener: %Span{} = opener
         },
         primary_span
       )
       when opener != primary_span,
       do: [pickup_label(opener, :secondary, "this local `where` block starts here")]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :where_binding_assign_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this local `where` block starts here"),
      pickup_label(previous, :secondary, "this is the local definition name")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :map_entry_separator_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    container = Map.get(context, :container, :map)

    [
      pickup_label(opener, :secondary, "this #{container} starts here"),
      pickup_label(Map.get(context, :entry_span), :secondary, "this #{container} entry starts here"),
      pickup_label(previous, :secondary, "the #{container} key ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :binary_generator_arrow_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this binary generator starts here"),
      pickup_label(previous, :secondary, "the binary pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :send_comma_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this send starts here"),
      pickup_label(previous, :secondary, "the send target ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :lift_callback_body_separator_missing,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this lifted callback starts here"),
      pickup_label(Map.get(context, :name_span), :secondary, "this is the callback name"),
      pickup_label(previous, :secondary, "the callback head ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :with_rematch_separator_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "the restated parent patterns start here"),
      pickup_label(previous, :secondary, "the final parent pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :record_field_colon_missing, previous: %Span{} = previous},
         primary_span
       )
       when previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "this is the record field name"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :local_function_keyword_missing, opener: %Span{} = opener},
         primary_span
       )
       when opener != primary_span,
       do: [%Label{span: opener, style: :secondary, message: "this starts a private declaration"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :implementation_for_keyword_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this starts the implementation"),
      pickup_label(previous, :secondary, "the implemented interface or protocol ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :fixity_colon_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this starts the fixity declaration"),
      pickup_label(previous, :secondary, "this is the operator being declared")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :precedencegroup_field_colon_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this is the precedence group"),
      pickup_label(previous, :secondary, "this is the setting name")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :type_declaration_assign_missing,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this starts the type declaration"),
      pickup_label(previous, :secondary, "the declaration head ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       )
       when kind in [
              :refinement_binder_invalid,
              :refinement_colon_missing,
              :refinement_bar_missing,
              :refinement_unclosed
            ] do
    [
      pickup_label(opener, :secondary, "this refinement type starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the refinement binder"),
      pickup_label(previous, :secondary, refinement_previous_label(kind))
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container}
         },
         primary_span
       )
       when container in [:splice, :splice_group] do
    [
      pickup_label(opener, :secondary, "the syntax splice starts here"),
      pickup_label(previous, :secondary, "the spliced expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :grouped_expression}
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this parenthesized expression starts here"),
      pickup_label(previous, :secondary, "the grouped expression ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container} = context
         },
         primary_span
       )
       when container in [:named_constructor_domain, :implicit_constructor_domain] do
    implicit? = container == :implicit_constructor_domain

    [
      pickup_label(
        opener,
        :secondary,
        if(implicit?,
          do: "this implicit constructor domain starts here",
          else: "this named constructor domain starts here"
        )
      ),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the dependent argument binder"),
      pickup_label(previous, :secondary, "the argument type ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :named_implicit_pattern} = context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this named implicit pattern starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the implicit binder"),
      pickup_label(previous, :secondary, "the implicit pattern ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :implicit_parameter} = context
         },
         primary_span
       ) do
    [
      pickup_label(opener, :secondary, "this implicit parameter starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the implicit parameter name"),
      pickup_label(previous, :secondary, "the parameter annotation ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :binary_specifier_arguments} = context
         },
         primary_span
       ) do
    [
      pickup_label(Map.get(context, :specifier_span), :secondary, "this is the binary specifier"),
      pickup_label(opener, :secondary, "its argument starts here"),
      pickup_label(previous, :secondary, "the specifier argument ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :selective_import}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "the selective import list starts here"),
      pickup_label(previous, :secondary, "the previous imported name ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: opener,
           previous: previous,
           context: %{container: container} = context
         },
         primary_span
       )
       when kind in [:container_opener_missing, :container_unclosed] and
              container in [:failure_parameters, :lift_callback_parameters] do
    owner = if container == :failure_parameters, do: "failure declaration", else: "lifted callback"

    opener_labels =
      if kind == :container_unclosed do
        [pickup_label(opener, :secondary, "the parameter list starts here")]
      else
        []
      end

    (opener_labels ++
       [
         pickup_label(Map.get(context, :owner_span), :secondary, "this #{owner} starts here"),
         pickup_label(Map.get(context, :name_span), :secondary, "this is its name"),
         pickup_label(previous, :secondary, "the previous parameter ends here")
       ])
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       )
       when kind in [
              :sigma_binder_invalid,
              :sigma_colon_missing,
              :sigma_comma_missing,
              :sigma_unclosed
            ] do
    [
      pickup_label(opener, :secondary, "this Sigma type starts here"),
      pickup_label(Map.get(context, :binder_span), :secondary, "this is the Sigma binder"),
      pickup_label(previous, :secondary, sigma_previous_label(kind))
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] and
              container in [:tuple_type, :tuple_type_sigil, :grouped_type] do
    opener_message =
      if container == :grouped_type, do: "this grouped type starts here", else: "this tuple type starts here"

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, "the previous type position ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "this parameter list starts here"),
      pickup_label(previous, :secondary, "the previous parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: container}
         },
         primary_span
       )
       when container in [:binary_literal, :binary_generator] do
    {opener_message, previous_message} =
      case container do
        :binary_literal -> {"this binary literal starts here", "the previous binary segment ends here"}
        :binary_generator -> {"this binary generator starts here", "its source expression ends here"}
      end

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, previous_message)
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :lambda_parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "this lambda parameter list starts here"),
      pickup_label(previous, :secondary, "the previous lambda parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :type_arguments}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "these type arguments start here"),
      pickup_label(previous, :secondary, "the previous type argument ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :type_parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "these type parameters start here"),
      pickup_label(previous, :secondary, "the previous type parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :constructor_parameters}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "this constructor's parameter list starts here"),
      pickup_label(previous, :secondary, "the previous constructor parameter ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: :container_unclosed,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :branch_block, family: family}
         },
         primary_span
       ) do
    opener_message =
      case family do
        :match -> "this inline match's branch block starts here"
        :with -> "this inline with's branch block starts here"
        :multi_with -> "this multi-scrutinee with's branch block starts here"
      end

    [
      pickup_label(opener, :secondary, opener_message),
      pickup_label(previous, :secondary, "the final branch ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: %{container: :type_indices}
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing] do
    [
      pickup_label(opener, :secondary, "these type indices start here"),
      pickup_label(previous, :secondary, "the previous type index ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous
         },
         primary_span
       )
       when kind in [:call_unclosed, :call_argument_separator_missing] do
    [
      pickup_label(opener, :secondary, "this call's argument list starts here"),
      pickup_label(previous, :secondary, "the previous argument ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(
         %SyntaxProblem{
           kind: kind,
           opener: %Span{} = opener,
           previous: previous,
           context: context
         },
         primary_span
       )
       when kind in [:container_unclosed, :container_separator_missing, :container_trailing_separator] do
    item = container_item_name(Map.get(context, :container))

    [
      pickup_label(opener, :secondary, "this container starts here"),
      pickup_label(previous, :secondary, "the previous #{item} ends here")
    ]
    |> Enum.reject(fn
      nil -> true
      %Label{span: span} -> span == primary_span
    end)
    |> Enum.uniq_by(& &1.span)
  end

  defp syntax_secondary_labels(%SyntaxProblem{opener: %Span{} = opener}, primary_span) when opener != primary_span,
    do: [%Label{span: opener, style: :secondary, message: "the construct starts here"}]

  defp syntax_secondary_labels(
         %SyntaxProblem{kind: :function_parameters_unparenthesized, previous: %Span{} = name},
         primary_span
       )
       when name != primary_span,
       do: [%Label{span: name, style: :secondary, message: "this function name needs a parameter list after it"}]

  defp syntax_secondary_labels(%SyntaxProblem{kind: kind, previous: %Span{} = previous}, primary_span)
       when kind in [:non_associative, :ambiguous_precedence] and previous != primary_span,
       do: [%Label{span: previous, style: :secondary, message: "the conflicting operator is here"}]

  defp syntax_secondary_labels(%SyntaxProblem{within: %Span{} = within}, primary_span) when within != primary_span,
    do: [%Label{span: within, style: :secondary, message: "while parsing this construct"}]

  defp syntax_secondary_labels(_problem, _primary_span), do: []

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :macro_use_mismatch,
           expected: {:literal, expected},
           context: %{token_type: token_type}
         },
         %Span{} = span
       )
       when token_type not in [:newline, :dedent, :eof] do
    [
      %Suggestion{
        message: "Replace it with `#{expected}`",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: to_string(expected)}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :function_parameters_unparenthesized, context: %{token_type: type}},
         %Span{} = span
       )
       when type in [:arrow, :assign, :newline, :eof] do
    insertion = %{span | end_byte: span.start_byte, end_line: span.start_line, end_column: span.start_column}

    [
      %Suggestion{
        message: "Insert `()` after the function name",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: insertion, replacement: "()"}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :lambda_arrow_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `->` before the lambda body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "-> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           context: %{family: :induction_case, token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=>` before the induction case body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "=> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :rewrite_using_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `using` before the equality proof",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "using "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :rewrite_in_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `in` before the expression to rewrite",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "in "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: kind, context: %{token_type: type}},
         %Span{} = span
       )
       when kind in [:macro_check_else_missing, :macro_check_fail_missing] and
              type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    {keyword, branch} =
      case kind do
        :macro_check_else_missing -> {"else", "the rejected branch"}
        :macro_check_fail_missing -> {"fail", "this failure value"}
      end

    [
      %Suggestion{
        message: "Insert `#{keyword}` before #{branch}",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "#{keyword} "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: kind, expected: expected, context: %{token_type: type}},
         %Span{} = span
       )
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] and type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `#{expected}` before this expression",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "#{expected} "}]
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: kind, expected: expected}, %Span{})
       when kind in [
              :macro_rule_becomes_missing,
              :literal_rule_becomes_missing,
              :computed_rule_by_missing,
              :macro_example_expands_missing,
              :macro_expands_with_missing
            ] do
    [
      %Suggestion{
        message: "Add `#{expected}` and the expression that follows it",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_indent_missing}, %Span{}) do
    [
      %Suggestion{
        message: "Indent one or more family members below the declaration",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_member_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Replace this line with a typed field, an `includes` line, or a `syntax` production",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_entry_invalid, context: %{valid_fields: fields}}, %Span{}) do
    [
      %Suggestion{
        message: "Start this entry with one of: #{inline_choices(fields)}",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :syntax_family_production_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Rewrite this entry using one of the syntax family's declared production forms",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :syntax_family_body_indent_missing, context: %{valid_fields: fields}},
         %Span{}
       ) do
    [
      %Suggestion{
        message: "Indent a structured body starting with one of: #{inline_choices(fields)}",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :macro_definition_entry_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Replace this line with a valid macro declaration entry",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :macro_example_entry_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Write `example use_site expands expected` on this line",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :macro_explain_point_invalid}, %Span{}) do
    [
      %Suggestion{
        message: "Write `Category => message` or `keyword \"word\" => message`",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :branch_arrow_missing,
           context: %{family: :explain_clause, token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=>` before the explanation message",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "=> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :branch_arrow_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `->` before the branch body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "-> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :gadt_constructor_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the constructor signature",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :assert_type_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `:` before the expected type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :named_implicit_pattern_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=` before the implicit pattern",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :local_binding_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=` before the binding value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :where_block_indent_missing}, %Span{}),
    do: [
      %Suggestion{
        message: "Indent each local definition beneath `where`",
        applicability: :manual
      }
    ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :where_binding_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `=` before the local value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :map_entry_separator_missing, context: %{ambiguous: true}},
         %Span{}
       ) do
    [
      %Suggestion{
        message: "Choose `,` for two punned entries or `=>` for a key-value entry",
        applicability: :manual
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :map_entry_separator_missing,
           context: %{token_type: type} = context
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    container = Map.get(context, :container, :map)

    [
      %Suggestion{
        message: "Insert `=>` before the #{container} value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "=> "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :binary_generator_arrow_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :binary_close, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `<-` before the generator source",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "<- "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :send_comma_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    [
      %Suggestion{
        message: "Insert `,` before the send message",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :lift_callback_body_separator_missing,
           expected: expected,
           context: %{token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen, :rbracket, :rbrace] do
    separator = if expected == :assign, do: "=", else: "->"

    [
      %Suggestion{
        message: "Insert `#{separator}` before the callback body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "#{separator} "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_opener_missing,
           observed: observed,
           context: %{container: container, token_type: type}
         },
         %Span{} = span
       )
       when container in [:failure_parameters, :lift_callback_parameters] do
    empty? = type in [:arrow, :assign, :newline, :dedent, :eof] or observed in ["returns", :returns]
    insertion = if empty?, do: "()", else: "("
    message = if empty?, do: "Insert an empty `()` parameter list", else: "Insert `(` before the first parameter"

    [
      %Suggestion{
        message: message,
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: insertion}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_opener_missing,
           context: %{container: :macro_obligation_capture}
         },
         %Span{} = span
       ) do
    [
      %Suggestion{
        message: "Insert `(` before the constrained capture",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "("}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :with_rematch_separator_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :arrow, :rbrace] do
    [
      %Suggestion{
        message: "Insert `|` before the with-pattern",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "| "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :type_indices_opener_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen] do
    [
      %Suggestion{
        message: "Insert `(` before the type indices",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "("}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :local_function_keyword_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `fn` before the local function name",
        applicability: :machine_applicable,
        edits: [
          %TextEdit{
            span: %{
              span
              | end_byte: span.start_byte,
                end_line: span.start_line,
                end_column: span.start_column
            },
            replacement: "fn "
          }
        ]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :implementation_for_keyword_missing, context: %{repair: :replace}},
         %Span{} = span
       ) do
    [
      %Suggestion{
        message: "Replace this keyword with `for`",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "for"}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :implementation_for_keyword_missing,
           context: %{repair: :insert, token_type: type}
         },
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    insertion_span = %{
      span
      | end_byte: span.start_byte,
        end_line: span.start_line,
        end_column: span.start_column
    }

    [
      %Suggestion{
        message: "Insert `for` before the implementation type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: insertion_span, replacement: "for "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :record_field_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the field type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :fixity_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the precedence group",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :precedencegroup_field_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline] do
    [
      %Suggestion{
        message: "Insert `:` before the setting value",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :type_declaration_assign_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent] do
    [
      %Suggestion{
        message: "Insert `=` before the type body",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "= "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :refinement_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rbrace] do
    [
      %Suggestion{
        message: "Insert `:` before the refinement's base type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :refinement_bar_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rbrace] do
    [
      %Suggestion{
        message: "Insert `|` before the refinement proposition",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: "| "}]
      }
    ]
  end

  defp syntax_insertions(%SyntaxProblem{kind: :refinement_binder_invalid}, %Span{}),
    do: [
      %Suggestion{
        message: "Replace this with a descriptive lower-case binder",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :sigma_binder_invalid}, %Span{}),
    do: [
      %Suggestion{
        message: "Replace this with a descriptive lower-case Sigma binder",
        applicability: :manual
      }
    ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :sigma_colon_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen] do
    [
      %Suggestion{
        message: "Insert `:` before the first value's type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ": "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :sigma_comma_missing, context: %{token_type: type}},
         %Span{} = span
       )
       when type not in [:eof, :dedent, :newline, :rparen] do
    [
      %Suggestion{
        message: "Insert `,` before the dependent result type",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rparen, context: %{container: :type_parameters}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rparen, context: %{container: :type_indices}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rbrace, context: %{container: :named_implicit_pattern}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rbrace, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: :rbrace, context: %{container: :implicit_parameter}},
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rbrace, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: :binary_specifier_arguments}
         },
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rbrace,
           context: %{container: :selective_import}
         },
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rbrace, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: container}
         },
         %Span{} = span
       )
       when container in [:splice, :splice_group] do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: container}
         },
         %Span{} = span
       )
       when container in [:failure_parameters, :lift_callback_parameters] do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{
           kind: :container_unclosed,
           expected: :rparen,
           context: %{container: :macro_obligation_capture}
         },
         %Span{} = span
       ) do
    closing_delimiter_insertion(:rparen, span)
  end

  defp syntax_insertions(%SyntaxProblem{observed: :eof, expected: expected}, %Span{} = span) do
    closing_delimiter_insertion(expected, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_unclosed, expected: expected, context: %{token_type: token_type}},
         %Span{} = span
       )
       when token_type in [:dedent, :newline] do
    closing_delimiter_insertion(expected, span)
  end

  defp syntax_insertions(
         %SyntaxProblem{kind: :mismatched_closer, expected: expected, observed: observed},
         %Span{} = span
       ) do
    replacement = syntax_insertion(expected)

    if replacement do
      [
        %Suggestion{
          message: "Replace #{syntax_name(observed)} with `#{replacement}`",
          applicability: :machine_applicable,
          edits: [%TextEdit{span: span, replacement: replacement}]
        }
      ]
    else
      []
    end
  end

  defp syntax_insertions(%SyntaxProblem{kind: kind}, %Span{})
       when kind in [:non_associative, :ambiguous_precedence],
       do: [
         %Suggestion{
           message: "Add parentheses around the operation that should happen first",
           applicability: :manual
         }
       ]

  defp syntax_insertions(%SyntaxProblem{kind: :unrecognized_pattern, observed: :range}, %Span{}),
    do: [
      %Suggestion{
        message: "Bind the value, then test its bounds with `when`",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :missing_function_body}, %Span{}),
    do: [
      %Suggestion{
        message: "Write an expression after `=`",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :invalid_parameter_name}, %Span{}),
    do: [
      %Suggestion{
        message: "Replace this with a descriptive lower-case parameter name",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :variadic_parameter_name_missing}, %Span{}),
    do: [
      %Suggestion{
        message: "Add a descriptive lower-case name after the variadic marker",
        applicability: :manual
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :call_argument_separator_missing}, %Span{} = span),
    do: [
      %Suggestion{
        message: "Insert `,` between these arguments",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :map}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these entries",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :record}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these fields",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :type_arguments}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these type arguments",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :type_parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these type parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :constructor_parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these constructor parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :type_indices}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these type indices",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :lambda_parameters}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these lambda parameters",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: :selective_import}},
         %Span{} = span
       ),
       do: [
         %Suggestion{
           message: "Insert `,` between these imported names",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(
         %SyntaxProblem{kind: :container_separator_missing, context: %{container: container}},
         %Span{} = span
       )
       when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
       do: [
         %Suggestion{
           message: "Insert `,` between these type positions",
           applicability: :machine_applicable,
           edits: [%TextEdit{span: span, replacement: ", "}]
         }
       ]

  defp syntax_insertions(%SyntaxProblem{kind: :container_separator_missing}, %Span{} = span),
    do: [
      %Suggestion{
        message: "Insert `,` between these elements",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ", "}]
      }
    ]

  defp syntax_insertions(%SyntaxProblem{kind: :container_trailing_separator}, %Span{} = span),
    do: [
      %Suggestion{
        message: "Remove the trailing comma",
        applicability: :machine_applicable,
        edits: [%TextEdit{span: span, replacement: ""}]
      }
    ]

  defp syntax_insertions(_problem, _span), do: []

  defp closing_delimiter_insertion(expected, span) do
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

  defp branch_family_name(:match_arm), do: "A pattern branch"
  defp branch_family_name(family) when family in [:pickup_clause, :pickup_else], do: "A pickup branch"
  defp branch_family_name(:function_clause), do: "A function clause"
  defp branch_family_name(family) when family in [:with_arm, :with_rematch_arm], do: "A with branch"

  defp refinement_previous_label(:refinement_bar_missing), do: "the base type ends here"
  defp refinement_previous_label(:refinement_unclosed), do: "the proposition ends here"
  defp refinement_previous_label(_kind), do: "this is the refinement binder"

  defp sigma_previous_label(:sigma_comma_missing), do: "the first value's type ends here"
  defp sigma_previous_label(:sigma_unclosed), do: "the dependent result type ends here"
  defp sigma_previous_label(_kind), do: "this is the Sigma binder"

  defp container_item_name(:map), do: "entry"
  defp container_item_name(:record), do: "field"
  defp container_item_name(:list_cons), do: "tail expression"
  defp container_item_name(:comprehension), do: "clause"
  defp container_item_name(:parameters), do: "parameter"
  defp container_item_name(:type_arguments), do: "type argument"
  defp container_item_name(:type_parameters), do: "type parameter"
  defp container_item_name(:constructor_parameters), do: "constructor parameter"
  defp container_item_name(:branch_block), do: "branch"
  defp container_item_name(:selective_import), do: "imported name"
  defp container_item_name(:type_indices), do: "type index"
  defp container_item_name(:lambda_parameters), do: "lambda parameter"

  defp container_item_name(container) when container in [:tuple_type, :tuple_type_sigil, :grouped_type],
    do: "type position"

  defp container_item_name(:binary_literal), do: "binary segment"
  defp container_item_name(:binary_generator), do: "source expression"
  defp container_item_name(_container), do: "element"

  defp syntax_insertion(:rparen), do: ")"
  defp syntax_insertion(:rbracket), do: "]"
  defp syntax_insertion(:rbrace), do: "}"
  defp syntax_insertion(:binary_close), do: ">>"

  defp syntax_insertion(:end), do: "end"
  defp syntax_insertion(:double_quote), do: "\""
  defp syntax_insertion(:single_quote), do: "'"
  defp syntax_insertion(:backtick), do: "`"
  defp syntax_insertion(_expected), do: nil

  defp missing_delimiter_kind(:rparen, :eof), do: :unclosed_parentheses
  defp missing_delimiter_kind(:rbracket, :eof), do: :unclosed_brackets
  defp missing_delimiter_kind(:rbrace, :eof), do: :unclosed_braces

  defp missing_delimiter_kind(expected, observed)
       when expected in [:rparen, :rbracket, :rbrace] and observed in [:rparen, :rbracket, :rbrace],
       do: :mismatched_closer

  defp missing_delimiter_kind(_expected, _observed), do: :unexpected_token

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

  defp surface_type(type) when is_binary(type), do: type
  defp surface_type(type), do: print_core(type)

  defp surface_pattern_annotation({:variable, _meta, name}), do: name_to_string(name)
  defp surface_pattern_annotation(type), do: surface_type(type)

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

  defp surface_declaration_name(name) do
    name
    |> name_to_string()
    |> String.split("#")
    |> List.last()
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)

  defp diagnostic_fingerprint(term) do
    term
    |> :erlang.term_to_binary()
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
    |> binary_part(0, 12)
  end

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

  defp maybe_put_meta_location(payload, meta) do
    case {Keyword.get(meta, :line), Keyword.get(meta, :col, Keyword.get(meta, :column))} do
      {line, column} when is_integer(line) and is_integer(column) ->
        Map.merge(payload, %{line: line, column: column})

      {line, _column} when is_integer(line) ->
        Map.put(payload, :line, line)

      _ ->
        payload
    end
  end

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
  defp syntax_name(:expression), do: "an expression"
  defp syntax_name(:identifier), do: "an identifier"
  defp syntax_name(:keyword), do: "a keyword"
  defp syntax_name(:integer), do: "an integer"
  defp syntax_name(:positive_integer), do: "a positive integer"
  defp syntax_name(:failure_constructor), do: "a failure constructor call"
  defp syntax_name(:family_field), do: "a typed field"
  defp syntax_name(:syntax_family_production), do: "a declared family production"
  defp syntax_name(:failure_category), do: "a failure category"
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

  defp authored_syntax(value) when is_integer(value) or is_float(value), do: "'#{value}'"
  defp authored_syntax(value), do: syntax_name(value)

  defp inline_choices([]), do: "no fields"
  defp inline_choices(values), do: Enum.map_join(values, ", ", &"`#{&1}`")
end
