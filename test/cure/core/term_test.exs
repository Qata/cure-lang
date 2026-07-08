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

  test "to_external/from_external round-trips every node kind into JSON-able maps" do
    terms = [
      {:type, 1},
      {:var, 3},
      {:pi, {:type, 0}, {:var, 0}},
      {:lam, {:type, 0}, {:var, 0}},
      {:app, {:var, 0}, {:var, 1}},
      {:sigma, {:type, 0}, {:var, 0}},
      {:pair, {:type, 0}, {:type, 1}},
      {:fst, {:var, 0}},
      {:snd, {:var, 0}},
      {:data, :SF, [{:type, 0}], [{:var, 0}]},
      {:ctor, :seq, [{:var, 0}, {:var, 1}]},
      {:case, {:var, 0}, {:lam, {:type, 0}, {:type, 0}},
       [{:prim, 0, {:type, 0}}, {:seq, 2, {:var, 1}}]},
      {:global, :and},
      {:eq, {:type, 0}, {:var, 0}, {:var, 0}},
      {:refl, {:var, 0}}
    ]

    for t <- terms do
      assert Term.term?(t), "test fixture #{inspect(t)} is not a valid term"
      ext = Term.to_external(t)
      assert is_map(ext), "external form of #{inspect(t)} must be a map"
      assert t == Term.from_external(ext)
    end
  end

  test "from_external interns only existing atoms — unknown symbol fails closed (K12 §D)" do
    # Untrusted JSON decode must not mint permanent atoms (atom-table-exhaustion
    # DoS — the table never shrinks). A name never interned in this VM fails
    # rather than creating an atom; symbols in any real term already exist and
    # still decode. NB: the "unseen" name must appear NOWHERE as an atom literal.
    assert_raise ArgumentError, fn ->
      Term.from_external(%{"node" => "global", "name" => "cure_k12_fe_unseen_qz"})
    end

    assert {:global, :and} == Term.from_external(%{"node" => "global", "name" => "and"})
  end
end
