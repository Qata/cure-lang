defmodule Antigen.Assays.SmtLintTest do
  use ExUnit.Case, async: false
  # async: false — these clauses spawn a Z3 subprocess (Cure.SMT.Process); serialize
  # to avoid subprocess contention with the parallel suite (spec §6, open item #3).

  alias Antigen.Assays.SmtLint
  alias Antigen.Challenge

  # --- inline MetaAST builders (Task 4's generator re-defines these) ---
  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp xvar, do: {:variable, [], "x"}
  defp bop(op, a, b), do: {:binary_op, [operator: op], [a, b]}
  # x > n
  defp gt(n), do: bop(:>, xvar(), lit(n))

  defp impl_ch(p1, p2) do
    Challenge.new(kind: :smt_query, assay: "smt/implication", label: :positive,
      payload: %{p1: p1, p2: p2, var: "x"}, seed: 1)
  end

  describe "eval_pred/2 (via public run behavior is enough, but sanity-check the oracle)" do
    # eval_pred is private; exercise it indirectly through a negative control whose
    # correctness depends on eval_pred computing the right truth values (Step-3 impl).
    test "oracle drives the false_discharge control (finds a witness in x>0 ∧ not x>5)" do
      # Enum.find walks @domain -32..32 ascending, so the witness it reports is
      # whichever is smallest in {1..5} (x=1) — assert the property, not a specific x.
      k = %{SmtLint.__real__() | prove_implication: fn _p1, _p2, _v, _b -> true end}
      assert {:violation, {:false_discharge, %{x: x}}} =
               SmtLint.run(impl_ch(gt(0), gt(5)), k)
      assert x > 0 and not (x > 5)
    end
  end

  describe "smt/implication (V6a)" do
    test "valid implication baseline: x > 5 ⇒ x > 0, real lint proves it, no bounded counterexample" do
      assert SmtLint.run(impl_ch(gt(5), gt(0))) == :ok
    end

    test "invalid implication baseline: x > 0 ⇒ x > 5, real lint returns false (or unknown) → no false discharge" do
      assert SmtLint.run(impl_ch(gt(0), gt(5))) == :ok
    end

    test "negative control: a prove_implication stub returning true on the invalid implication" do
      k = %{SmtLint.__real__() | prove_implication: fn _p1, _p2, _v, _b -> true end}
      assert {:violation, {:false_discharge, _}} = SmtLint.run(impl_ch(gt(0), gt(5)), k)
    end
  end
end
