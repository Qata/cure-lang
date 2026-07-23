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

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

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
