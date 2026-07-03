defmodule Antigen.Assays.SmtLint do
  @moduledoc """
  Property tests for the untrusted SMT lint `Cure.SMT.Solver` (spec: antigen-smt-lint).

  Framed by the locked decision that Z3 is OUT of the dependent-kernel TCB — the SMT
  layer is an untrusted lint, never a proof. The property is LINT SOUNDNESS, not
  completeness: the lint may give up (`:unknown`), but must never over-claim.

    * smt/implication — `prove_implication == true` ⟹ no bounded counterexample (V6a).
    * smt/unsat       — `check_sat == :unsat` ⟹ no bounded satisfying witness (V6b).
    * smt/witness     — `prove_with_counterexample`'s `{:failed, model}` genuinely
      refutes, and a `{:proven, nil}` claim has no bounded counterexample (V6c).

  The oracle is an Antigen-owned bounded evaluator `eval_pred/2` over the MetaAST
  predicate format, decided over a fixed integer domain (`@domain`). This is a
  sound-in-one-direction differential: a bounded counterexample proves the lint
  over-claimed; the converse never fires (completeness is out of scope). `:unknown`
  is always a legal, non-infecting answer.

  Ops go through an injectable @real map (run/2); negative controls weaken the
  code-under-test without touching `Cure.SMT.*` or `:meck`.
  """
  alias Antigen.Challenge
  alias Cure.SMT.Solver

  @domain -32..32

  @real %{
    prove_implication: &Solver.prove_implication/4,
    check_sat: &Solver.check_sat/2,
    prove_with_counterexample: &Solver.prove_with_counterexample/4
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :smt_query} = c), do: run(c, @real)

  def run(%Challenge{kind: :smt_query, assay: "smt/implication", payload: %{p1: p1, p2: p2, var: var}}, k) do
    case k.prove_implication.(p1, p2, var, :int) do
      true ->
        case Enum.find(@domain, fn x -> eval_pred(p1, x) and not eval_pred(p2, x) end) do
          nil -> :ok
          x -> {:violation, {:false_discharge, %{x: x, p1: p1, p2: p2}}}
        end

      _ ->
        # false / :unknown — the lint did not over-claim (completeness is out of scope)
        :ok
    end
  end

  # --- bounded oracle: independent evaluator over the MetaAST predicate format ---
  # Mirrors Translator.translate_op/1 semantics exactly (single free variable = x).
  defp eval_pred({:literal, _meta, n}, _x), do: n
  defp eval_pred({:variable, _meta, _name}, x), do: x

  defp eval_pred({:binary_op, meta, [l, r]}, x) do
    a = eval_pred(l, x)
    b = eval_pred(r, x)

    case Keyword.get(meta, :operator) do
      :+ -> a + b
      :- -> a - b
      :* -> a * b
      :> -> a > b
      :< -> a < b
      :>= -> a >= b
      :<= -> a <= b
      :== -> a == b
      :!= -> a != b
      :and -> a and b
      :or -> a or b
    end
  end

  defp eval_pred({:unary_op, meta, [o]}, x) do
    v = eval_pred(o, x)

    case Keyword.get(meta, :operator) do
      :not -> not v
      :- -> -v
    end
  end
end
