defmodule Cure.Core.BranchUnifyTest do
  @moduledoc """
  Unit tests for the public branch_unify/4 wrapper (spec §3). It reuses the
  private unify_indices/4; these pin the three verdicts, the compound-solved
  case the elaborator consumes for constructor-headed refinement (§6 Slice
  3(i)), and the wrapper's own dname/cname family-mismatch guard.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Inductive, Kernel, Eval}

  # Dec = Dcoupled | Causal ;  Ix(n:Dec) with wrap : (p:Dec) -> Ix(Causal)
  @dec {:data, :Dec, [], []}

  defp sig do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Dec, [], [], 0),
      [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
    )
    |> Inductive.declare(
      Inductive.family(:Ix, [], [{:n, @dec}], 0),
      [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])]
    )
  end

  defp causal_val, do: Eval.eval({:ctor, :Causal, []}, [])
  defp dcoupled_val, do: Eval.eval({:ctor, :Dcoupled, []}, [])

  test ":trivial when the scrutinee index equals wrap's ground result index (Causal)" do
    ctx = Context.empty(sig())
    assert :trivial = Kernel.branch_unify(ctx, :Ix, :wrap, [causal_val()])
  end

  test ":impossible on a rigid ground clash (wrap's Causal vs scrutinee Dcoupled)" do
    ctx = Context.empty(sig())
    assert :impossible = Kernel.branch_unify(ctx, :Ix, :wrap, [dcoupled_val()])
  end

  test "{:solved, subst} binds a bare outer scrutinee index var to wrap's compound result index" do
    # ctx has one outer binder (a Dec); its value is a neutral var reified as {:var,0}.
    ctx = Context.extend(Context.empty(sig()), Eval.eval(@dec, []))
    outer_idx_val = {:vneutral, {:nvar, 0}}
    assert {:solved, subst} = Kernel.branch_unify(ctx, :Ix, :wrap, [outer_idx_val])
    # The outer index var (shifted past wrap's 1 arg → key 1) is bound to Causal.
    assert subst == %{1 => {:ctor, :Causal, []}}
  end

  test ":impossible on an index-vector arity mismatch — Enum.zip must not truncate (#573)" do
    # `wrap` has exactly ONE result index (Causal). Passing a scrutinee index
    # vector of a different length is an arity mismatch. `Enum.zip` would
    # silently truncate to the common prefix and verdict :trivial, ignoring the
    # surplus/missing index — a soundness hole. A length mismatch is a definite
    # non-unification: :impossible.
    ctx = Context.empty(sig())
    assert :impossible = Kernel.branch_unify(ctx, :Ix, :wrap, [causal_val(), causal_val()])
    assert :impossible = Kernel.branch_unify(ctx, :Ix, :wrap, [])
  end

  test ":impossible when cname exists but does not belong to dname's family" do
    # Dcoupled/Causal are Dec's own constructors, not Ix's — a caller passing the
    # wrong dname for a real cname must not silently get a verdict computed
    # against the wrong family's schema (the wrapper is new TCB code; its own
    # doc comment already guards the "unknown constructor" case, so the
    # "known constructor of a different family" case must be guarded too).
    ctx = Context.empty(sig())
    assert :impossible = Kernel.branch_unify(ctx, :Ix, :Causal, [causal_val()])
  end
end
