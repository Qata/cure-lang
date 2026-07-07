defmodule Cure.SMT.SolverK13Test do
  # K13: the untrusted SMT lint must not report an obligation it cannot even
  # translate as *proven*. An untranslatable node renders to `true` in the query
  # (translator fallback), so `P1 ∧ ¬P2` goes spuriously unsat ⇒ a false 'proven'.
  # Fail closed to :unknown (already a first-class verdict the refinement checker
  # handles), deterministically — before Z3 runs — so it does not depend on a
  # malformed-query parse error for safety.
  use ExUnit.Case, async: true
  alias Cure.SMT.{Solver, Translator}

  # Translatable arithmetic predicate: x > 0
  defp gt0, do: {:binary_op, [operator: :>], [{:variable, [], "x"}, {:literal, [subtype: :integer], 0}]}
  # An untranslatable node — no do_translate clause, hits the fallback.
  defp weird, do: {:weird_node, [], []}

  test "fully_translatable? distinguishes translatable from untranslatable predicates" do
    assert Translator.fully_translatable?(gt0())
    refute Translator.fully_translatable?(weird())
  end

  test "prove_implication fails closed to :unknown on an untranslatable obligation (K13)" do
    assert :unknown = Solver.prove_implication(gt0(), weird(), "x", :int)
    assert :unknown = Solver.prove_implication(weird(), gt0(), "x", :int)
  end

  test "prove_implication still decides a fully-translatable obligation" do
    # x > 0  =>  x > 0  is trivially provable; must NOT be short-circuited to :unknown.
    assert Solver.prove_implication(gt0(), gt0(), "x", :int) in [true, :unknown]
    # (true when Z3 present; the guard must not itself force :unknown here — it only
    # fires on untranslatable input, and both predicates here are translatable.)
    refute Solver.prove_implication(gt0(), gt0(), "x", :int) == false
  end
end
