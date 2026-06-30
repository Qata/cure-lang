defmodule Cure.Core.TermTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Term

  test "constructs and recognises core nodes" do
    assert Term.term?({:type, 0})
    assert Term.term?({:var, 0})
    assert Term.term?({:pi, {:type, 0}, {:var, 0}})
    assert Term.term?({:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}})
    refute Term.term?({:type, 3})
    refute Term.term?({:var, -1})
    refute Term.term?(:not_a_term)
  end

  test "shift lifts free vars at/above the cutoff, leaves bound vars" do
    # closed term (body var #0 is bound by the λ) is unchanged by shifting
    assert {:lam, {:type, 0}, {:var, 0}} == Term.shift({:lam, {:type, 0}, {:var, 0}}, 1, 0)
    # a free var at/above the cutoff is lifted by the amount
    assert {:var, 2} == Term.shift({:var, 0}, 2, 0)
  end

  test "subst replaces the target index under binders, leaves others" do
    # `λ. #1`: the body var #1 refers to the OUTER binder. Substituting index 0
    # with a CLOSED replacement must descend under the one binder (target -> 1)
    # and replace #1.
    assert {:lam, {:type, 0}, {:type, 1}} ==
             Term.subst({:lam, {:type, 0}, {:var, 1}}, 0, {:type, 1})

    # `λ. #0`: body var #0 is bound by the λ itself, so substituting outer index 0
    # must NOT touch it (capture-avoidance via binder-depth shift).
    assert {:lam, {:type, 0}, {:var, 0}} ==
             Term.subst({:lam, {:type, 0}, {:var, 0}}, 0, {:type, 1})

    # no-op when the target index does not occur.
    assert {:type, 0} == Term.subst({:type, 0}, 0, {:type, 1})
  end
end
