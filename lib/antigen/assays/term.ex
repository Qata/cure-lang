defmodule Antigen.Assays.Term do
  @moduledoc """
  The Tier-B differential self-consistency assays (spec §7). Each consumes a
  `:typed_term` challenge and probes the kernel against itself:

    * term/infer_check       — infer(t)=A ⟹ check(t,A)=:ok ∧ A ≡ claimed T
    * term/subject_reduction — nf(t) still checks at A
    * term/normalization     — nf(nf t)=nf t, nf t re-checks, C2 round-trips

  Fuel exhaustion at any stage is its own violation class `{:fuel_exhausted,
  stage}` — a suspected non-normalization, never conflated with a mismatch.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Kernel, Normalise, Conv, Serialize, Context}

  @assay_fuel 500
  def assay_fuel, do: @assay_fuel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :typed_term, assay: assay, payload: p}) do
    env = SigMenu.env_of(p.sig)
    ctx = SigMenu.rebuild_context(env, p.ctx)

    case Kernel.infer(ctx, p.term) do
      {:ok, inferred} -> dispatch(assay, ctx, p, inferred)
      {:error, e} -> {:violation, {:infer_failed, e}}
    end
  end

  # --- term/infer_check ------------------------------------------------------
  defp dispatch("term/infer_check", ctx, p, inferred) do
    depth = Context.length(ctx)
    inferred_term = Normalise.quote(inferred, depth)

    cond do
      Kernel.check(ctx, p.term, inferred) != :ok ->
        {:violation, {:check_disagrees, Kernel.check(ctx, p.term, inferred)}}

      not converges?(inferred_term, p.type, ctx) ->
        {:violation, {:inferred_type_mismatch, inferred_term, p.type}}

      true -> :ok
    end
  end

  # --- term/subject_reduction ------------------------------------------------
  # `fuel: @assay_fuel` is required, not cosmetic: `Normalise.nf/3`'s default
  # (2-arg call) is `fuel: :infinity`, which would make `:fuel_exhausted`
  # below permanently unreachable — silently defeating locked decision #6
  # ("fixed committed fuel decides verdicts") and this module's own moduledoc
  # claim that fuel exhaustion is its own violation class.
  defp dispatch("term/subject_reduction", ctx, p, inferred) do
    case Normalise.nf(ctx, p.term, fuel: @assay_fuel) do
      :fuel_exhausted -> {:violation, {:fuel_exhausted, :nf}}
      nf ->
        case Kernel.check(ctx, nf, inferred) do
          :ok -> :ok
          err -> {:violation, {:nf_ill_typed, err}}
        end
    end
  end

  # --- term/normalization ----------------------------------------------------
  defp dispatch("term/normalization", ctx, p, inferred) do
    with nf when nf != :fuel_exhausted <- Normalise.nf(ctx, p.term, fuel: @assay_fuel),
         nf2 when nf2 != :fuel_exhausted <- Normalise.nf(ctx, nf, fuel: @assay_fuel) do
      cond do
        nf2 != nf -> {:violation, {:not_idempotent, nf, nf2}}
        Kernel.check(ctx, nf, inferred) != :ok -> {:violation, {:nf_ill_typed, nf}}
        not round_trips?(nf) -> {:violation, {:c2_round_trip, nf}}
        true -> :ok
      end
    else
      :fuel_exhausted -> {:violation, {:fuel_exhausted, :nf}}
    end
  end

  defp converges?(t1, t2, ctx) do
    case Conv.conv_within?(t1, t2, Context.env(ctx), Context.length(ctx),
           Context.signature(ctx), @assay_fuel) do
      {:ok, true} -> true
      _ -> false
    end
  end

  defp round_trips?(term) do
    case Serialize.decode(Serialize.encode(term)) do
      {:ok, ^term} -> true
      _ -> false
    end
  end
end
