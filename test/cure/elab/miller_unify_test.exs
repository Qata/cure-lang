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
end
