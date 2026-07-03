defmodule Cure.Core.UnifyIndicesTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context}
  alias Cure.Elab.Program

  @src "mod M\n  type Nat = Z | S(Nat)\n  type SameLen indices (n: Nat, m: Nat)\n    same : SameLen(k, k)\nend\n"

  defp sig, do: (fn -> {:ok, s} = Program.elaborate(@src); s end).()

  test "matching `same : SameLen(k,k)` against SameLen(a,b) forces b := a" do
    s = sig()
    # Two `Context.extend` calls give two outer vars: `a` (extended first) at
    # level 0, `b` (extended second) at level 1. `branch_unify`'s scrut_indices
    # are VALUES (levels); `unify_indices` reifies them to indices internally.
    ctx =
      Context.empty(s)
      |> Context.extend({:vdata, :Nat, []})
      |> Context.extend({:vdata, :Nat, []})

    # scrutinee index VALUES for [a, b] (SameLen(a, b)).
    scrut = [{:vneutral, {:nvar, 0}}, {:vneutral, {:nvar, 1}}]
    assert {:solved, subst} = Kernel.branch_unify(ctx, :SameLen, :same, scrut)
    # `same` has arity 1 (the implicit `k`); the forced entry keys the OUTER var (>= arity).
    forced = subst |> Map.to_list() |> Enum.filter(fn {k, _v} -> k >= 1 end)
    assert forced != []
    assert {_k, {:var, _}} = hd(forced)
  end

  # --- Guard tests (Step 5): occurs / injectivity / conflict / no-regression ---

  # Families used by the guard tests. `box : Box(k)` gives a pure ctor-arg-only
  # solve; `vs : Vone(S(k))` exercises same-ctor injectivity; `vz : Vone(Z)`
  # exercises a rigid-head conflict.
  @guard_src "mod G\n  type Nat = Z | S(Nat)\n  type Box indices (n: Nat)\n    box : Box(k)\n  type Vone indices (n: Nat)\n    vs : Vone(S(k))\n    vz : Vone(Z)\nend\n"

  defp guard_sig, do: (fn -> {:ok, s} = Program.elaborate(@guard_src); s end).()

  defp one_var_ctx(s), do: Context.extend(Context.empty(s), {:vdata, :Nat, []})

  # Does any key of `subst` occur in its own bound value? (a cyclic binding)
  defp cyclic?(subst) do
    Enum.any?(subst, fn {k, v} -> occurs?(k, v) end)
  end

  defp occurs?(key, {:var, k}), do: k == key
  defp occurs?(key, t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&occurs?(key, &1))
  defp occurs?(key, l) when is_list(l), do: Enum.any?(l, &occurs?(key, &1))
  defp occurs?(_key, _), do: false

  test "(a) occurs/cycle: `same : SameLen(k,k)` vs SameLen(a, S(a)) never binds a cyclic key" do
    s = sig()
    # Single outer var `a`; second scrutinee index is the ctor value `S(a)`.
    ctx = one_var_ctx(s)
    scrut = [{:vneutral, {:nvar, 0}}, {:vctor, :S, [{:vneutral, {:nvar, 0}}]}]
    verdict = Kernel.branch_unify(ctx, :SameLen, :same, scrut)
    # Verdict may be {:solved,_} (conservative) or :undecided-driven :trivial/solved,
    # but must NEVER be :impossible-by-cycle and must NEVER bind a cyclic key.
    case verdict do
      {:solved, subst} -> refute cyclic?(subst)
      :trivial -> :ok
      other -> flunk("unexpected verdict for occurs case: #{inspect(other)}")
    end
  end

  test "(b) injectivity: `vs : Vone(S(k))` vs Vone(S(a)) decomposes to k := a" do
    s = guard_sig()
    ctx = one_var_ctx(s)
    scrut = [{:vctor, :S, [{:vneutral, {:nvar, 0}}]}]
    assert {:solved, subst} = Kernel.branch_unify(ctx, :Vone, :vs, scrut)
    # arity 1: the ctor-arg key 0 is solved to the scrutinee var; no cyclic bind.
    assert Map.has_key?(subst, 0)
    assert {:var, _} = Map.get(subst, 0)
    refute cyclic?(subst)
  end

  test "(c) conflict: `vz : Vone(Z)` vs Vone(S(a)) is :impossible" do
    s = guard_sig()
    ctx = one_var_ctx(s)
    scrut = [{:vctor, :S, [{:vneutral, {:nvar, 0}}]}]
    assert :impossible = Kernel.branch_unify(ctx, :Vone, :vz, scrut)
  end

  test "(d) no-regression: plain ctor-arg-only `box : Box(k)` vs Box(a) has no forced entry" do
    s = guard_sig()
    ctx = one_var_ctx(s)
    scrut = [{:vneutral, {:nvar, 0}}]
    assert {:solved, subst} = Kernel.branch_unify(ctx, :Box, :box, scrut)
    # Exactly the prior behavior: ctor-arg key (< arity 1) := scrutinee var; no
    # forced scrutinee-var (>= arity) entries induced.
    assert {:var, _} = Map.get(subst, 0)
    forced = subst |> Map.to_list() |> Enum.filter(fn {k, _v} -> k >= 1 end)
    assert forced == []
  end
end
