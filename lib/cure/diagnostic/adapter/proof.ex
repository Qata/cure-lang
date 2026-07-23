defmodule Cure.Diagnostic.Adapter.Proof do
  @moduledoc "Converts proof-chain failures into authored diagnostics."

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    Label,
    ProofChainMismatchProblem,
    ProofChainSyntaxProblem,
    RewriteProblem,
    SimplificationProblem,
    Span,
    Suggestion,
    TextEdit
  }

  @spec from_error(term(), keyword()) :: Diagnostic.t()
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
      primary: primary(opts, label),
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
      primary: primary(opts, label),
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
      primary: primary(opts, label),
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
      primary: primary(opts, label),
      secondary: simplification_labels(problem, Keyword.get(opts, :span)),
      payload: problem
    )
  end

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      _ -> nil
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

  defp simplification_labels(problem, primary) do
    [{problem.command, "simplify command"}, {problem.rule, "rule supplied here"}]
    |> Enum.flat_map(fn
      {%Span{} = span, message} when span != primary -> [%Label{span: span, style: :secondary, message: message}]
      _ -> []
    end)
  end

  defp simplification_body(message, problem, opts) do
    goals =
      if problem.before_surface && problem.after_surface,
        do: "\n\nBefore: #{problem.before_surface}\nAfter: #{problem.after_surface}",
        else: ""

    supplied =
      if problem.kind == :proof_mismatch and problem.simplified_supplied_surface,
        do: "\nSupplied proof simplifies to: #{problem.simplified_supplied_surface}",
        else: ""

    if Keyword.get(opts, :trace) == :expanded and (problem.trace_ids || []) != [] do
      ids = Enum.map_join(problem.trace_ids, ", ", &to_string/1)
      Doc.paragraph(message <> goals <> supplied <> "\n\nSimplification trace: " <> ids)
    else
      Doc.paragraph(message <> goals <> supplied)
    end
  end

  defp rewrite_suggestions(%RewriteProblem{kind: :ambiguous_occurrence, command: %Span{} = command} = problem) do
    insertion = %{
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
          {%{
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
end
