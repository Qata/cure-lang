defmodule Cure.Elab.ProofGoal do
  @moduledoc "Typed, compile-time-only state for compositional proof commands."

  alias Cure.Core.{Context, Eval, Grade, Kernel, Quote}
  alias Cure.Diagnostic.{ProofChainMismatchProblem, ProofChainSyntaxProblem, RewriteProblem}
  alias Cure.Elab.{Elaborator, Rewrite, Subst}
  alias Cure.MetaAST.Metadata

  @enforce_keys [:expected, :names, :context, :env, :source, :status, :builders, :trace]
  defstruct [:expected, :names, :context, :env, :source, :status, :builders, :trace]

  @type status :: :open | :closed
  @type t :: %__MODULE__{
          expected: Cure.Core.Term.t(),
          names: [String.t()],
          context: Cure.Core.Context.t(),
          env: Cure.Core.Env.t(),
          source: term(),
          status: status(),
          builders: [term()],
          trace: [term()]
        }

  @type command_result :: {:open, t()} | {:closed, Cure.Core.Term.t(), [term()]} | {:error, term()}

  def run({:proof_justification, meta, statements}, expected, names, context, env, step_index) do
    goal = %__MODULE__{
      expected: expected,
      names: names,
      context: context,
      env: env,
      source: meta,
      status: :open,
      builders: [],
      trace: []
    }

    execute(statements, goal, step_index)
  end

  defp execute([], %__MODULE__{status: :open} = goal, step_index) do
    info = Metadata.source_info(goal.source)

    {:error,
     {:proof_chain_mismatch,
      %ProofChainMismatchProblem{
        kind: :unfinished_justification,
        step_index: step_index,
        justification: info && info.whole,
        residual_goal: goal.expected,
        cause: {:open_goal, fact_names(goal.builders)}
      }}}
  end

  defp execute([statement | rest], %__MODULE__{status: :open} = goal, step_index) do
    case command(statement, goal) do
      {:open, next_goal} ->
        execute(rest, next_goal, step_index)

      {:closed, evidence, trace} when rest == [] ->
        {:ok, evidence, trace}

      {:closed, _evidence, trace} ->
        first_unreachable = hd(rest)
        closed_at = trace |> List.last() |> trace_span()

        {:error,
         {:proof_chain_syntax,
          %ProofChainSyntaxProblem{
            kind: :unreachable_proof_statement,
            construct: closed_at || surface_span(goal.source),
            step: surface_span(first_unreachable),
            observed: expression_kind(first_unreachable),
            expected: :end_of_justification
          }}}

      {:error, _} = error ->
        error
    end
  end

  defp command({:assignment, meta, [{:variable, _, name}, _rhs]} = statement, goal)
       when is_list(meta) do
    if Keyword.get(meta, :have, false) do
      {:open,
       %{
         goal
         | names: [name | goal.names],
           builders: goal.builders ++ [statement],
           trace: goal.trace ++ [{:have, name, surface_span(statement)}]
       }}
    else
      close_with_expression(statement, goal)
    end
  end

  defp command({:rewrite_command, meta, [proof_ast]}, goal) do
    case Keyword.get(meta, :target, :goal) do
      :goal -> rewrite_goal(proof_ast, meta, goal, nil)
      {:at, occurrence} -> rewrite_goal(proof_ast, meta, goal, occurrence)
      {:in, name} -> rewrite_hypothesis(proof_ast, meta, goal, name)
    end
  end

  defp command(statement, goal), do: close_with_expression(statement, goal)

  defp close_with_expression(statement, goal) do
    {surface_builders, transports} = Enum.split_with(goal.builders, &match?({:assignment, _, _}, &1))
    block = {:block, [], surface_builders ++ [statement]}
    original_names = Enum.drop(goal.names, length(surface_builders))

    case Elaborator.elaborate_expr_checked(block, goal.expected, original_names, goal.context, goal.env) do
      {:ok, evidence} ->
        evidence = Enum.reduce(Enum.reverse(transports), evidence, &apply_builder/2)

        {:closed, evidence, goal.trace ++ [{:exact, surface_span(statement)}]}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp rewrite_hypothesis(proof_ast, meta, goal, name) do
    with index when is_integer(index) <- Enum.find_index(goal.names, &(&1 == name)),
         hypothesis_value when not is_nil(hypothesis_value) <- Context.lookup(goal.context, index),
         hypothesis = Kernel.normalize(goal.context, Quote.reify(hypothesis_value, Context.length(goal.context))),
         {:ok, proof, proof_type} <- Elaborator.elaborate_expr_typed(proof_ast, goal.names, goal.context, goal.env),
         {:ok, ty_value, a_value, b_value} <- Rewrite.eq_parts(proof_type, Context.signature(goal.context)),
         depth = Context.length(goal.context),
         ty = Kernel.normalize(goal.context, Quote.reify(ty_value, depth)),
         a = Kernel.normalize(goal.context, Quote.reify(a_value, depth)),
         b = Kernel.normalize(goal.context, Quote.reify(b_value, depth)),
         {:ok, transform, rewritten, occurrences} <-
           Rewrite.directed_transform(proof, ty, a, b, hypothesis, Keyword.fetch!(meta, :direction)),
         evidence = transform.({:var, index}),
         rewritten_value = Eval.eval(rewritten, Context.env(goal.context)),
         :ok <- Kernel.check(goal.context, evidence, rewritten_value) do
      {:open,
       %{
         goal
         | names: [name | goal.names],
           expected: Subst.shift(goal.expected, 1, 0),
           context: Context.extend_def(goal.context, rewritten_value, Eval.eval(evidence, Context.env(goal.context))),
           builders: goal.builders ++ [{:core_fact, rewritten, evidence}],
           trace: goal.trace ++ [{:rewrite_hypothesis, name, occurrences, surface_span(meta)}]
       }}
    else
      nil ->
        rewrite_error(:bad_target, meta, proof_ast, goal, target: name)

      {:error, {:no_occurrence, occurrences}} ->
        rewrite_error(:no_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:ambiguous_occurrence, occurrences}} ->
        rewrite_error(:ambiguous_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:reverse_only, direction}} ->
        rewrite_error(:reverse_only, meta, proof_ast, goal, direction: direction)

      {:error, cause} ->
        rewrite_error(:theorem_not_equality, meta, proof_ast, goal, cause: cause)
    end
  end

  defp apply_builder({:transport, build}, evidence), do: build.(evidence)
  defp apply_builder({:core_fact, type, value}, body), do: {:let, Grade.unrestricted(), type, value, body}

  defp rewrite_goal(proof_ast, meta, goal, occurrence) do
    surface_builders = Enum.filter(goal.builders, &match?({:assignment, _, _}, &1))
    proof_block = {:block, [], surface_builders ++ [proof_ast]}
    original_names = Enum.drop(goal.names, length(surface_builders))
    depth = Context.length(goal.context)

    with {:ok, proof, proof_type} <-
           Elaborator.elaborate_expr_typed(proof_block, original_names, goal.context, goal.env),
         {:ok, ty_value, a_value, b_value} <- Rewrite.eq_parts(proof_type, Context.signature(goal.context)),
         ty = Kernel.normalize(goal.context, Quote.reify(ty_value, depth)),
         a = Kernel.normalize(goal.context, Quote.reify(a_value, depth)),
         b = Kernel.normalize(goal.context, Quote.reify(b_value, depth)),
         expected = Kernel.normalize(goal.context, goal.expected),
         {:ok, build, rewritten, occurrences} <-
           Rewrite.directed_plan(proof, ty, a, b, expected, Keyword.fetch!(meta, :direction), occurrence) do
      {:open,
       %{
         goal
         | expected: rewritten,
           builders: goal.builders ++ [{:transport, build}],
           trace: goal.trace ++ [{:rewrite, Keyword.fetch!(meta, :direction), occurrences, surface_span(meta)}]
       }}
    else
      {:error, {:no_occurrence, occurrences}} ->
        rewrite_error(:no_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:ambiguous_occurrence, occurrences}} ->
        rewrite_error(:ambiguous_occurrence, meta, proof_ast, goal, occurrences: occurrences)

      {:error, {:invalid_occurrence, selected, occurrences}} ->
        rewrite_error(:invalid_occurrence, meta, proof_ast, goal, target: selected, occurrences: occurrences)

      {:error, {:reverse_only, direction}} ->
        rewrite_error(:reverse_only, meta, proof_ast, goal, direction: direction)

      {:error, cause} ->
        rewrite_error(:theorem_not_equality, meta, proof_ast, goal, cause: cause)
    end
  end

  defp rewrite_error(kind, meta, proof_ast, goal, fields) do
    problem =
      struct!(
        RewriteProblem,
        Keyword.merge(
          [
            kind: kind,
            command: surface_span(meta),
            theorem: surface_span(proof_ast),
            goal: surface_span(goal.source),
            occurrences: [],
            target: Keyword.get(meta, :target, :goal),
            direction: Keyword.get(meta, :direction, :forward)
          ],
          fields
        )
      )

    {:error, {:rewrite_failed, problem}}
  end

  defp fact_names(builders) do
    Enum.flat_map(builders, fn
      {:assignment, _meta, [{:variable, _, name}, _rhs]} -> [name]
      _ -> []
    end)
  end

  defp surface_span(meta) when is_list(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp surface_span({_tag, meta, _children}) when is_list(meta), do: surface_span(meta)
  defp surface_span(_other), do: nil

  defp expression_kind({kind, _meta, _children}) when is_atom(kind), do: kind
  defp expression_kind(_other), do: :expression

  defp trace_span({_kind, span}), do: span
  defp trace_span({_kind, _name, span}), do: span
  defp trace_span(_other), do: nil
end
