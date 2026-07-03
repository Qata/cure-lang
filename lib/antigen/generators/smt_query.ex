defmodule Antigen.Generators.SmtQuery do
  @moduledoc """
  Fixed catalogs of MetaAST predicate queries for the `Antigen.Assays.SmtLint`
  families (spec: antigen-smt-lint). Deterministic, no corpus banking.

  All entries are inside decidable one-variable linear integer arithmetic and are
  chosen so the real Z3 lint answers soundly (clean catalog re-checks `:ok`). The
  negative-witness implication that surfaces the `Cure.SMT.Parser` negative-value
  bug is intentionally NOT here — it is a known-finding fixture in `smt_lint_test.exs`
  (mirrors V4's erased-first ctor/def fixtures).
  """
  alias Antigen.Challenge

  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp xvar, do: {:variable, [], "x"}
  defp bop(op, a, b), do: {:binary_op, [operator: op], [a, b]}
  defp gt(n), do: bop(:>, xvar(), lit(n))
  defp lt(n), do: bop(:<, xvar(), lit(n))

  @doc "V6a — implication soundness catalog."
  @spec implication_challenges() :: [Challenge.t()]
  def implication_challenges do
    [
      impl(gt(5), gt(0), 0),   # valid: x>5 ⇒ x>0
      impl(gt(0), gt(5), 1)    # invalid: real lint returns false → no false discharge
    ]
  end

  @doc "V6b — unsat soundness catalog."
  @spec unsat_challenges() :: [Challenge.t()]
  def unsat_challenges do
    [
      unsat(bop(:and, gt(0), lt(0)), 2),  # unsat: x>0 ∧ x<0
      unsat(gt(0), 3)                     # sat: real lint returns :sat → :ok
    ]
  end

  @doc "V6c — witness consistency catalog (non-negative counterexamples only)."
  @spec witness_challenges() :: [Challenge.t()]
  def witness_challenges do
    [
      witness(gt(0), gt(5), 4)  # counterexample space {1..5}, all non-negative
    ]
  end

  defp impl(p1, p2, seed) do
    Challenge.new(kind: :smt_query, assay: "smt/implication", label: :positive,
      payload: %{p1: p1, p2: p2, var: "x"}, seed: seed)
  end

  defp unsat(constraint, seed) do
    Challenge.new(kind: :smt_query, assay: "smt/unsat", label: :positive,
      payload: %{constraint: constraint, var: "x"}, seed: seed)
  end

  defp witness(p1, p2, seed) do
    Challenge.new(kind: :smt_query, assay: "smt/witness", label: :positive,
      payload: %{p1: p1, p2: p2, var: "x"}, seed: seed)
  end
end
