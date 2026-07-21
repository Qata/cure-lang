defmodule Cure.Elab.ProofGoal do
  @moduledoc "Typed, compile-time-only state for compositional proof commands."

  alias Cure.Diagnostic.{ProofChainMismatchProblem, ProofChainSyntaxProblem}
  alias Cure.Elab.Elaborator
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

  defp command(statement, goal), do: close_with_expression(statement, goal)

  defp close_with_expression(statement, goal) do
    block = {:block, [], goal.builders ++ [statement]}
    original_names = Enum.drop(goal.names, length(goal.builders))

    case Elaborator.elaborate_expr_checked(block, goal.expected, original_names, goal.context, goal.env) do
      {:ok, evidence} -> {:closed, evidence, goal.trace ++ [{:exact, surface_span(statement)}]}
      {:error, reason} -> {:error, reason}
    end
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
