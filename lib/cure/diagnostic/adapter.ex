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

  def from_error({:codegen_error, reason}, opts), do: from_error(reason, opts)

  def from_error({:parse_error, [reason | _]}, opts), do: from_error(reason, opts)

  def from_error({:source_context, reason, context}, opts) when is_map(context) do
    opts =
      opts
      |> Keyword.put(:checking, Map.get(context, :checking))
      |> then(fn opts ->
        case Map.get(context, :span) do
          %Span{} = span -> Keyword.put(opts, :span, span)
          _ -> opts
        end
      end)

    from_error(reason, opts)
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
          Doc.paragraph([
            "Expected",
            Doc.emphasis(:expected, expected_surface),
            "but found",
            Doc.concat([Doc.emphasis(:observed, actual_surface), Doc.text(".")])
          ])
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
      message: "Expected `#{expected_surface}`, but found `#{actual_surface}`.",
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

  @spec unknown_name(atom(), term(), keyword()) :: Diagnostic.t()
  def unknown_name(namespace, name, opts \\ []) do
    spelling = name_to_string(name)
    candidates = opts |> Keyword.get(:candidates, []) |> Enum.map(&name_to_string/1) |> Enum.uniq()

    Diagnostic.new(
      code: @unknown_name_code,
      key: :unknown_name,
      severity: :error,
      title: "Unknown #{namespace_title(namespace)}",
      message: "`#{spelling}` is not available in this #{namespace} namespace.",
      primary: primary_label(opts, "`#{spelling}` was not found"),
      notes: Keyword.get(opts, :notes, []),
      suggestions: candidate_suggestions(candidates),
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        namespace: namespace,
        name: spelling,
        candidates: candidates,
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
    [
      %Suggestion{
        message: "Did you mean #{Enum.map_join(candidates, ", ", &"`#{&1}`")}?",
        applicability: :maybe_incorrect
      }
    ]
  end

  defp namespace_title(:value), do: "value"
  defp namespace_title(:constructor), do: "constructor"
  defp namespace_title(:type), do: "type"
  defp namespace_title(:module), do: "module"
  defp namespace_title(:member), do: "module member"
  defp namespace_title(other), do: to_string(other)

  defp type_problem_title(%ExpectationOrigin{kind: :annotation}), do: "Annotation does not match"
  defp type_problem_title(%ExpectationOrigin{kind: :branch}), do: "Branches have different types"
  defp type_problem_title(%ExpectationOrigin{kind: :condition}), do: "Condition is not boolean"
  defp type_problem_title(%ExpectationOrigin{kind: :call_argument}), do: "Argument has the wrong type"
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

  defp syntax_problem_context(%SyntaxProblem{kind: :recovered_statement, observed: observed}),
    do:
      "The parser could not continue this statement after #{syntax_name(observed)}, so it resumed at the next statement boundary."

  defp syntax_problem_context(%SyntaxProblem{observed: :eof}),
    do: "The source ended while I was still parsing this construct."

  defp syntax_problem_context(%SyntaxProblem{observed: observed}),
    do: "#{String.capitalize(syntax_name(observed))} cannot appear at this point in the construct."

  defp syntax_expected_doc(%SyntaxProblem{expected: nil, alternatives: []}), do: Doc.empty()

  defp syntax_expected_doc(%SyntaxProblem{} = problem) do
    expected = [problem.expected | problem.alternatives] |> Enum.reject(&is_nil/1) |> Enum.map(&syntax_name/1)

    Doc.paragraph([
      "A valid continuation here starts with",
      Doc.emphasis(:expected, Enum.join(expected, " or ")) |> then(&Doc.concat([&1, Doc.text(".")]))
    ])
  end

  defp syntax_problem_label(%SyntaxProblem{kind: :unterminated_lambda}), do: "the unclosed body reaches here"
  defp syntax_problem_label(%SyntaxProblem{kind: :recovered_statement}), do: "parsing resumed after this token"
  defp syntax_problem_label(_problem), do: "this syntax does not fit here"

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

  defp type_problem_context(%ExpectationOrigin{kind: :branch}),
    do: "Every branch of this expression must produce the same type."

  defp type_problem_context(%ExpectationOrigin{kind: :condition}),
    do: "A condition must produce `Bool` before either branch can run."

  defp type_problem_context(%ExpectationOrigin{kind: :call_argument, index: index, owner: owner}),
    do: "Argument #{display_index(index)} of `#{name_to_string(owner || "this function")}` has an incompatible type."

  defp type_problem_context(%ExpectationOrigin{kind: :operator_operand, owner: owner}),
    do: "The `#{name_to_string(owner || "operator")}` operator cannot use this operand type."

  defp type_problem_context(_origin), do: "This expression has a different type than its context requires."

  defp type_problem_label(%ExpectationOrigin{kind: :condition}), do: "this condition has the wrong type"
  defp type_problem_label(%ExpectationOrigin{kind: :branch}), do: "this branch disagrees with another branch"
  defp type_problem_label(%ExpectationOrigin{kind: :call_argument}), do: "this argument has the wrong type"
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

  defp syntax_name(name) when is_atom(name), do: "`#{name}`"
  defp syntax_name(name), do: inspect(name)
end
