defmodule Antigen.Assays.IndexedTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Indexed, as: A
  alias Antigen.Generators.Indexed, as: G

  test "4.1 well-typed branch-family case is accepted (no violation)" do
    assert :ok == A.run(G.branch_family(:well_typed))
  end

  test "4.1 ill-typed foreign-branch case must be rejected by the kernel" do
    # SOUNDNESS assertion: the kernel must NOT accept a Dec case with a Foo branch.
    # If this returns a {:wrongly_accepted, _} violation, the kernel has a hole —
    # apply the family-scoping fix, then this returns :ok.
    assert :ok == A.run(G.branch_family(:ill_typed))
  end

  test "4.2 exhaustive Tri case is accepted" do
    assert :ok == A.run(G.coverage(:well_typed))
  end

  test "4.2 non-exhaustive Tri case must be rejected" do
    assert :ok == A.run(G.coverage(:ill_typed))
  end

  test "4.3 ill-typed wrap-branch (wrong body type) must be rejected" do
    assert :ok == A.run(G.refinement(:ill_typed))
  end

  test "4.3 refinement-complete well-typed case is now accepted (completeness fix)" do
    # Pre-fix this replayed {:wrongly_rejected, {:refine, :branch_type}} (the
    # documented incompleteness). unify_indices now solves n := Causal from the
    # wrap ctor's ground result index and refines h : Ix n to Ix Causal.
    assert :ok == A.run(G.refinement(:well_typed))
  end

  test "4.4 well-formed motive is accepted" do
    assert :ok == A.run(G.motive_wf(:well_typed))
  end

  test "4.4 over-applied (malformed) motive must be rejected" do
    assert :ok == A.run(G.motive_wf(:ill_typed))
  end
end
