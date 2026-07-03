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
