defmodule Cure.Elab.MillerUnifyTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{MetaCtx, Unify}

  # Higher-order (Miller) pattern unification: `?m x̄ := λx̄. t`. Exercised through
  # the public `unify/4` by unifying two Π types, so the metavariable-applied-to-a-
  # bound-variable constraint arises under the binder (depth 1). The abstraction
  # domains come from the metavariable's recorded type.

  @nat {:data, :Nat, [], []}
  # ?m : (Nat) -> Type
  defp fam_ctx, do: MetaCtx.fresh(MetaCtx.new(), {:pi, @nat, {:type, 0}})

  test "constant solution: ?m(n) =? Nat  ⇒  ?m := λ_:Nat. Nat" do
    {ctx, m} = fam_ctx()
    t1 = {:pi, @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, @nat, @nat}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, @nat, @nat} == Unify.zonk({:meta, m}, ctx2)
  end

  test "identity solution: ?m(n) =? n  ⇒  ?m := λn:Nat. n" do
    {ctx, m} = fam_ctx()
    t1 = {:pi, @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, @nat, {:var, 0}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, @nat, {:var, 0}} == Unify.zonk({:meta, m}, ctx2)
  end

  test "escape: ?m() applied to no bound var is not a Miller pattern (falls through)" do
    # A bare metavariable (no application) uses the ordinary first-order solve.
    {ctx, m} = fam_ctx()
    assert {:ok, ctx2} = Unify.unify({:meta, m}, @nat, ctx, nil)
    assert @nat == Unify.zonk({:meta, m}, ctx2)
  end

  test "no metavariable type recorded ⇒ Miller falls through (no crash, no solve)" do
    # fresh/1 records nil type; peel_pi_domains cannot supply domains, so the
    # higher-order case falls through to the first-order rules and fails cleanly.
    {ctx, m} = MetaCtx.fresh(MetaCtx.new())
    t1 = {:pi, @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, @nat, @nat}
    assert {:error, _} = Unify.unify(t1, t2, ctx, nil)
  end

  # Structurally-rich solutions: the solution body carries a type-former, so the
  # abstraction step (`mabs`) must recurse THROUGH a binder-introducing node and
  # keep the pattern var's de Bruijn level correct. A depth bug here would abstract
  # the wrong variable and produce an unsound metavariable solution.

  test "Pi solution: ?m(n) =? (Πk:Nat. Nat)  ⇒  ?m := λn. Πk:Nat. Nat" do
    {ctx, m} = fam_ctx()
    t1 = {:pi, @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, @nat, {:pi, @nat, @nat}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, @nat, {:pi, @nat, @nat}} == Unify.zonk({:meta, m}, ctx2)
  end

  test "Sigma solution: ?m(n) =? (Σk:Nat. Nat)  ⇒  ?m := λn. Σk:Nat. Nat" do
    {ctx, m} = fam_ctx()
    t1 = {:pi, @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, @nat, {:sigma, @nat, @nat}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, @nat, {:sigma, @nat, @nat}} == Unify.zonk({:meta, m}, ctx2)
  end

  test "Eq solution binding the pattern var: ?m(n) =? Eq Nat n n  ⇒  ?m := λn. Eq Nat n n" do
    # The bound var n appears INSIDE the Eq — mabs must abstract it (var 0 under the
    # solution's λ), not leave it dangling or escape. A wrong depth yields the wrong
    # endpoint.
    {ctx, m} = fam_ctx()
    t1 = {:pi, @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, @nat, {:eq, @nat, {:var, 0}, {:var, 0}}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, @nat, {:eq, @nat, {:var, 0}, {:var, 0}}} == Unify.zonk({:meta, m}, ctx2)
  end

  test "indexed-family solution: ?m(n) =? Vec n  ⇒  ?m := λn. Vec n (index abstracted)" do
    # The pattern var flows into a family INDEX position. mabs's `:data` clause must
    # recurse into the index list and abstract n there — the dependent-inference case
    # (a metavariable resolved to an indexed type).
    {ctx, m} = fam_ctx()
    t1 = {:pi, @nat, {:app, {:meta, m}, {:var, 0}}}
    t2 = {:pi, @nat, {:data, :Vec, [], [{:var, 0}]}}

    assert {:ok, ctx2} = Unify.unify(t1, t2, ctx, nil)
    assert {:lam, @nat, {:data, :Vec, [], [{:var, 0}]}} == Unify.zonk({:meta, m}, ctx2)
  end
end
