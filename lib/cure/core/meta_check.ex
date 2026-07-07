defmodule Cure.Core.MetaCheck do
  @moduledoc """
  Metatheory regression harnesses for the trusted Core (K11a): subject reduction
  (#638) and progress (#639). These are property predicates driven over corpora
  by the harness test files; they are guardrails, not proofs, and each corpus
  grows as later waves land.
  """

  alias Cure.Core.{Kernel, Conv, Context}

  @doc """
  Subject reduction (#638): `term` infers a type, its normal form infers a type,
  and the two types are definitionally equal. False if ill-typed or fuel-exhausted.
  """
  @spec type_preserved?(Context.t(), tuple()) :: boolean()
  def type_preserved?(ctx, term) do
    with {:ok, ty1} <- Kernel.infer(ctx, term),
         nf when nf != :fuel_exhausted <- Kernel.normalize(ctx, term),
         {:ok, ty2} <- Kernel.infer(ctx, nf) do
      Conv.conv_values?(ty1, ty2, Context.length(ctx), Context.signature(ctx))
    else
      _ -> false
    end
  end
end
