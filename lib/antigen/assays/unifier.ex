defmodule Antigen.Assays.Unifier do
  @moduledoc """
  Property tests for the two untrusted unification engines against the trusted
  kernel (spec: antigen-unifier-soundness).

    * unify/soundness       — Elab.Unify: zonked sides are Conv-convertible (V2a).
    * unify/intrinsic       — Elab.Unify: occurs / idempotent-zonk / meta-closed.
    * unify_types/fixpoint  — Types.Unify: re-unifying the substituted sides needs
                              no new bindings (self-consistency; no external oracle).
    * unify_types/intrinsic — Types.Unify: occurs / idempotent-apply / var-elim.

  Every engine op goes through an injectable @real map (run/2) so negative controls
  weaken the code-under-test without touching the engines or using :meck. The
  re-check op (tu_reunify) is split from the solve op (tu_unify) so a systematically
  buggy solve is caught by a real re-check.
  """
  alias Antigen.Challenge
  alias Cure.Elab.{Unify, MetaCtx}
  alias Cure.Types.Unify, as: TUnify
  alias Cure.Core.{Conv, Normalise}

  @assay_fuel 500_000
  @real %{
    eu_unify: &Unify.unify/4,
    eu_zonk: &Unify.zonk/2,
    eu_solution: &MetaCtx.solution/2,
    conv: &Conv.conv?/5,
    tu_unify: &TUnify.unify/3,
    tu_reunify: &TUnify.unify/3,
    tu_apply: &TUnify.apply_subst/2
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :unify_problem} = c), do: run(c, @real)

  def run(%Challenge{kind: :unify_problem, assay: "unify/soundness", payload: p}, k) do
    case k.eu_unify.(p.t1, p.t2, p.ctx, p.sig) do
      {:error, _} ->
        :ok

      {:ok, ctx2} ->
        z1 = k.eu_zonk.(p.t1, ctx2)
        z2 = k.eu_zonk.(p.t2, ctx2)

        cond do
          not (meta_free?(z1) and meta_free?(z2)) ->
            {:violation, {:unify_unsound, {:meta_survived, p.t1}, p.t2}}

          Normalise.with_fuel(@assay_fuel, fn -> k.conv.(z1, z2, [], 0, p.sig) end) == true ->
            :ok

          true ->
            {:violation, {:unify_unsound, p.t1, p.t2}}
        end
    end
  end

  def run(%Challenge{kind: :unify_problem, assay: "unify/intrinsic", payload: p}, k) do
    case k.eu_unify.(p.t1, p.t2, p.ctx, p.sig) do
      {:error, _} ->
        :ok

      {:ok, ctx2} ->
        z1 = k.eu_zonk.(p.t1, ctx2)
        z2 = k.eu_zonk.(p.t2, ctx2)

        cond do
          Enum.any?(p.meta_ids, fn id -> cyclic_solution?(id, ctx2, k) end) ->
            {:violation, {:occurs, p.meta_ids}}

          k.eu_zonk.(z1, ctx2) != z1 or k.eu_zonk.(z2, ctx2) != z2 ->
            {:violation, {:zonk_not_idempotent, p.t1}}

          not (meta_free?(z1) and meta_free?(z2)) ->
            {:violation, {:meta_not_eliminated, p.t1}}

          true ->
            :ok
        end
    end
  end

  def run(%Challenge{kind: :unify_problem, assay: "unify_types/fixpoint", payload: p}, k) do
    case k.tu_unify.(p.t1, p.t2, %{}) do
      {:error, _, _} ->
        :ok

      {:ok, s, _} ->
        a = k.tu_apply.(p.t1, s)
        b = k.tu_apply.(p.t2, s)

        case k.tu_reunify.(a, b, s) do
          {:ok, s2, _} when s2 == s -> :ok
          _ -> {:violation, {:solution_unstable, p.t1, p.t2}}
        end
    end
  end

  def run(%Challenge{kind: :unify_problem, assay: "unify_types/intrinsic", payload: %{expect: :error} = p}, k) do
    case k.tu_unify.(p.t1, p.t2, %{}) do
      {:error, _, _} -> :ok
      {:ok, _, _} -> {:violation, {:occurs_not_detected, p.t1, p.t2}}
    end
  end

  def run(%Challenge{kind: :unify_problem, assay: "unify_types/intrinsic", payload: p}, k) do
    case k.tu_unify.(p.t1, p.t2, %{}) do
      {:error, _, _} ->
        :ok

      {:ok, s, _} ->
        a = k.tu_apply.(p.t1, s)
        keys = Map.keys(s)

        cond do
          k.tu_apply.(a, s) != a -> {:violation, {:apply_not_idempotent, p.t1}}
          has_solved_var?(a, keys) -> {:violation, {:var_not_eliminated, p.t1}}
          true -> :ok
        end
    end
  end

  defp has_solved_var?({:type_var, n}, keys), do: n in keys
  defp has_solved_var?({:list, a}, keys), do: has_solved_var?(a, keys)
  defp has_solved_var?({:tuple, ts}, keys), do: Enum.any?(ts, &has_solved_var?(&1, keys))
  defp has_solved_var?({:fun, ps, r}, keys), do: Enum.any?(ps, &has_solved_var?(&1, keys)) or has_solved_var?(r, keys)
  defp has_solved_var?({:adt, _n, ps}, keys), do: Enum.any?(ps, &has_solved_var?(&1, keys))
  defp has_solved_var?({:map, kk, v}, keys), do: has_solved_var?(kk, keys) or has_solved_var?(v, keys)
  defp has_solved_var?({:refinement, base, _, _}, keys), do: has_solved_var?(base, keys)
  defp has_solved_var?(_, _keys), do: false

  # Read the solution for `id` ONCE through the op-map, then check structurally
  # whether {:meta, id} occurs in it — WITHOUT following further solutions (a cyclic
  # eu_solution stub would otherwise loop forever). nil solution = unsolved = clean.
  defp cyclic_solution?(id, ctx, k) do
    case k.eu_solution.(ctx, id) do
      nil -> false
      sol -> occurs_raw?(id, sol)
    end
  end

  defp occurs_raw?(id, {:meta, id}), do: true
  defp occurs_raw?(_id, {:meta, _}), do: false
  defp occurs_raw?(id, {:ctor, _c, args}), do: Enum.any?(args, &occurs_raw?(id, &1))
  defp occurs_raw?(id, {:data, _f, ps, is}), do: Enum.any?(ps ++ is, &occurs_raw?(id, &1))
  defp occurs_raw?(id, {:app, f, x}), do: occurs_raw?(id, f) or occurs_raw?(id, x)
  defp occurs_raw?(id, {:pi, d, c}), do: occurs_raw?(id, d) or occurs_raw?(id, c)
  defp occurs_raw?(id, {:lam, d, b}), do: occurs_raw?(id, d) or occurs_raw?(id, b)
  defp occurs_raw?(_id, _), do: false

  # local, independent of Elab.Unify's private meta_free?/1
  defp meta_free?({:meta, _}), do: false
  defp meta_free?({:data, _f, ps, is}), do: Enum.all?(ps ++ is, &meta_free?/1)
  defp meta_free?({:ctor, _c, args}), do: Enum.all?(args, &meta_free?/1)
  defp meta_free?({:app, f, x}), do: meta_free?(f) and meta_free?(x)
  defp meta_free?({:pi, d, c}), do: meta_free?(d) and meta_free?(c)
  defp meta_free?({:lam, d, b}), do: meta_free?(d) and meta_free?(b)
  defp meta_free?({:sigma, d, c}), do: meta_free?(d) and meta_free?(c)
  defp meta_free?(_), do: true
end
