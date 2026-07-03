defmodule Antigen.Assays.UnifierTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Unifier, Challenge}
  alias Antigen.Generators.UnifyProblem
  alias Cure.Elab.MetaCtx

  defp z0, do: {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}
  defp pair(a, b), do: {:ctor, :Pair, [a, b]}
  defp m(n), do: {:meta, n}

  defp sound_ch(t1, t2, meta_ids) do
    Challenge.new(kind: :unify_problem, assay: "unify/soundness", label: :translatable,
      payload: %{t1: t1, t2: t2, ctx: MetaCtx.new(), sig: nil, meta_ids: meta_ids}, seed: 1)
  end

  test "V2a soundness baseline: ?0 vs S Z solves and zonked sides are Conv-equal" do
    assert Unifier.run(sound_ch(m(0), s(z0()), [0])) == :ok
  end

  test "V2a soundness structural: Pair(?0, Z) vs Pair(S Z, ?1) — nested solve, Conv-equal" do
    assert Unifier.run(sound_ch(pair(m(0), z0()), pair(s(z0()), m(1)), [0, 1])) == :ok
  end

  test "V2a soundness negative control: an eu_unify stub that solves ?0 to the WRONG ctor infects" do
    ch = sound_ch(m(0), s(z0()), [0])
    # claims success but solves ?0 := Z, not S Z -> zonked sides Z vs S Z, not Conv-equal
    k = %{Unifier.__real__() | eu_unify: fn _t1, _t2, ctx, _sig -> {:ok, MetaCtx.put_solution(ctx, 0, z0())} end}
    assert {:violation, {:unify_unsound, _, _}} = Unifier.run(ch, k)
  end

  test "V2a soundness negative control: an eu_unify stub that claims success without solving anything leaves a meta behind" do
    ch = sound_ch(m(0), s(z0()), [0])
    # claims success but stores no solution at all -> zonk(?0) is still {:meta,0},
    # not meta-free -> distinct branch from the wrong-ctor control above
    k = %{Unifier.__real__() | eu_unify: fn _t1, _t2, ctx, _sig -> {:ok, ctx} end}
    assert {:violation, {:unify_unsound, {:meta_survived, _}, _}} = Unifier.run(ch, k)
  end

  describe "unify/intrinsic (V2a)" do
    defp intr_ch(t1, t2, meta_ids) do
      Challenge.new(kind: :unify_problem, assay: "unify/intrinsic", label: :translatable,
        payload: %{t1: t1, t2: t2, ctx: MetaCtx.new(), sig: nil, meta_ids: meta_ids}, seed: 1)
    end

    test "baseline: occurs-clean, zonk idempotent, metas eliminated" do
      assert Unifier.run(intr_ch(m(0), s(z0()), [0])) == :ok
      assert Unifier.run(intr_ch(pair(m(0), z0()), pair(s(z0()), m(1)), [0, 1])) == :ok
    end

    test "occurs negative control: a cyclic eu_solution stub infects" do
      ch = intr_ch(m(0), s(z0()), [0])
      # id 0's 'solution' contains {:meta, 0} -> cyclic
      k = %{Unifier.__real__() | eu_solution: fn _ctx, 0 -> s(m(0)); _ctx, _ -> nil end}
      assert {:violation, {:occurs, _}} = Unifier.run(ch, k)
    end

    test "zonk-idempotence negative control: an eu_zonk stub that re-wraps its output each call infects" do
      ch = intr_ch(m(0), s(z0()), [0])
      # always adds another ExtraWrap layer on top of the real zonk -> re-zonking a
      # zonked term is never a fixed point
      k = %{Unifier.__real__() | eu_zonk: fn t, ctx -> {:ctor, :ExtraWrap, [Cure.Elab.Unify.zonk(t, ctx)]} end}
      assert {:violation, {:zonk_not_idempotent, _}} = Unifier.run(ch, k)
    end

    test "meta-closed negative control: an identity eu_zonk stub that never substitutes solutions away infects" do
      ch = intr_ch(m(0), s(z0()), [0])
      # identity is trivially idempotent (passes the zonk-idempotence check above)
      # but leaves the solved metavariable ?0 in place -> not meta-free
      k = %{Unifier.__real__() | eu_zonk: fn t, _ctx -> t end}
      assert {:violation, {:meta_not_eliminated, _}} = Unifier.run(ch, k)
    end
  end
end
