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

  describe "smt/unsat (V6b)" do
    # x > 0 ∧ x < 0  — unsatisfiable
    defp conj(a, b), do: bop(:and, a, b)
    defp lt(n), do: bop(:<, xvar(), lit(n))

    defp sat_ch(constraint) do
      Challenge.new(kind: :smt_query, assay: "smt/unsat", label: :positive,
        payload: %{constraint: constraint, var: "x"}, seed: 1)
    end

    test "unsat baseline: x > 0 ∧ x < 0 is unsat, no bounded witness → :ok" do
      assert SmtLint.run(sat_ch(conj(gt(0), lt(0)))) == :ok
    end

    test "sat baseline: x > 0 is sat (lint returns :sat not :unsat) → :ok" do
      assert SmtLint.run(sat_ch(gt(0))) == :ok
    end

    test "negative control: a check_sat stub returning :unsat on the satisfiable x > 0" do
      k = %{SmtLint.__real__() | check_sat: fn _ast, _vt -> :unsat end}
      assert {:violation, {:false_unsat, %{x: x}}} = SmtLint.run(sat_ch(gt(0)), k)
      assert x > 0
    end
  end

  describe "smt/witness (V6c)" do
    defp witness_ch(p1, p2) do
      Challenge.new(kind: :smt_query, assay: "smt/witness", label: :positive,
        payload: %{p1: p1, p2: p2, var: "x"}, seed: 1)
    end

    test "witness baseline: invalid x > 0 ⇒ x > 5 yields a genuine (non-negative) counterexample → :ok" do
      # counterexample space x ∈ {1..5} — strictly non-negative, so the real
      # Parser returns a clean integer (dodges the negative-value parser bug).
      assert SmtLint.run(witness_ch(gt(0), gt(5))) == :ok
    end

    test "negative control: a prove_with_counterexample stub returning a non-refuting integer model" do
      # x=99 satisfies BOTH x>0 and x>5, so it is NOT a counterexample to x>0 ⇒ x>5.
      k = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:failed, %{"x" => 99}} end}
      assert {:violation, {:bogus_counterexample, _}} = SmtLint.run(witness_ch(gt(0), gt(5)), k)
    end

    test "unusable-model control: a stub returning a non-integer (malformed) model value" do
      k = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:failed, %{"x" => "(- 7"}} end}
      assert {:violation, {:unusable_model, _}} = SmtLint.run(witness_ch(gt(0), gt(5)), k)
    end

    test "proven/unknown are legal: a stub returning {:proven, nil} or {:unknown, nil} → :ok" do
      k1 = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:proven, nil} end}
      k2 = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:unknown, nil} end}
      assert SmtLint.run(witness_ch(gt(5), gt(0)), k1) == :ok
      assert SmtLint.run(witness_ch(gt(0), gt(5)), k2) == :ok
    end

    test "negative control: a prove_with_counterexample stub returning {:proven, nil} on the invalid implication" do
      # x > 0 ⇒ x > 5 is invalid (x=1 refutes it). A stub falsely claiming :proven is a
      # false-proven soundness violation — symmetric to V6a's false_discharge, but this
      # exercises prove_with_counterexample's OWN proven-claim path (a different code
      # path/query from prove_implication; reconciliation #4 explains why V6a's control
      # does not already cover this).
      k = %{SmtLint.__real__() | prove_with_counterexample: fn _p1, _p2, _v, _b -> {:proven, nil} end}
      assert {:violation, {:false_proven, %{x: x}}} = SmtLint.run(witness_ch(gt(0), gt(5)), k)
      assert x > 0 and not (x > 5)
    end
  end

  describe "parse_model negative-witness — FIXED, now a regression guard (real Solver + real Parser)" do
    # x > -100 ⇒ x >= 0 : counterexample space x ∈ {-99..-1} — STRICTLY negative,
    # so Z3 must return a negative witness. This once surfaced the real
    # Cure.SMT.Parser.parse_model/1 bug (negative `(- N)` truncated to the malformed
    # string "(- N"), which the assay reported as {:unusable_model, _}. The parser's
    # value-capture regex is now fixed, so the negative witness parses to a genuine
    # integer that refutes the implication → the assay returns :ok. Kept as a
    # regression guard: it goes red again if the truncation is reintroduced.
    defp ge(n), do: bop(:>=, xvar(), lit(n))

    test "real prove_with_counterexample on a negative-witness implication now yields a usable, refuting model (regression guard)" do
      ch = Challenge.new(kind: :smt_query, assay: "smt/witness", label: :negative,
        payload: %{p1: gt(-100), p2: ge(0), var: "x"}, seed: 99)
      assert SmtLint.run(ch) == :ok
    end
  end

  describe "generator + runner wiring" do
    alias Antigen.Generators.SmtQuery
    alias Antigen.Runner

    test "each catalog is non-empty and correctly tagged" do
      assert SmtQuery.implication_challenges() != []
      assert SmtQuery.unsat_challenges() != []
      assert SmtQuery.witness_challenges() != []
      assert Enum.all?(SmtQuery.implication_challenges(), & &1.assay == "smt/implication")
      assert Enum.all?(SmtQuery.unsat_challenges(), & &1.assay == "smt/unsat")
      assert Enum.all?(SmtQuery.witness_challenges(), & &1.assay == "smt/witness")
    end

    test "runner dispatches all three ids and the whole clean catalog is :ok" do
      all =
        SmtQuery.implication_challenges() ++
          SmtQuery.unsat_challenges() ++ SmtQuery.witness_challenges()

      assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
    end
  end
end
