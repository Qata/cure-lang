defmodule Antigen.Generators.DeltaReduce do
  @moduledoc """
  Known-normal-form generator for the `delta/nf` vertical
  (`Antigen.Assays.DeltaReduce`): δ-reduction (unfolding of CERTIFIED global
  definitions) under the trusted normalizer, checked against a
  correct-by-construction normal form.

  This is the definitional-equality path nothing else in the suite drives — the
  closed-`typed_term` verticals normalize terms over the v1 menu, which has no
  global definitions, so `Normalise.unfold_certified_head` (δ-unfold a certified
  global) and its ι-follow-through on the unfolded body (a projection landing on
  the pair a def expands to) stay cold. Over a fixed certified env
  (`idnat = λx.x`, `kpair = (Z, S Z)`) the true normal form is computable by
  construction, so each case pins `nf(term)` exactly.
  """
  alias Antigen.{Gen, Challenge}

  @z {:ctor, :Z, []}
  defp s(t), do: {:ctor, :S, [t]}

  # {term, expected_nf, note}
  @cases [
    {{:app, {:global, :idnat}, @z}, @z,
     "δ+β: idnat Z → Z (unfold certified global, then β)"},
    {{:app, {:global, :idnat}, {:ctor, :S, [@z]}}, {:ctor, :S, [@z]},
     "δ+β: idnat (S Z) → S Z"},
    {{:fst, {:global, :kpair}}, @z,
     "δ+ι: fst kpair → Z (unfold to a pair, project first — nfst)"},
    {{:snd, {:global, :kpair}}, {:ctor, :S, [@z]},
     "δ+ι: snd kpair → S Z (project second — nsnd)"},
    {{:app, {:global, :idnat}, {:fst, {:global, :kpair}}}, @z,
     "nested: idnat (fst kpair) → Z (two unfolds + a projection)"}
  ]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@cases), fn {term, expected, note} ->
      Gen.return(
        Challenge.new(
          kind: :delta_reduce,
          assay: "delta/nf",
          label: :reduces,
          payload: %{term: term, expected: expected},
          note: note
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end
