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
  @nat {:data, :Nat, [], []}

  # `kpair : Sigma(Nat, const-Nat) = mk_pair(Z, S Z)` (the inductive dependent pair,
  # D2). Projections are single-branch `:case`s over `mk_pair` — the ncase form the
  # δ+ι engine reduces now that the primitive `{:fst}`/`{:snd}` nodes are retired
  # (`case (mk_pair x y) of mk_pair(x,y) -> x|y` ι-reduces exactly as nfst/nsnd did).
  # Motive is the constant `Nat` (the pair is non-dependent); fields bind x=`{:var,1}`,
  # y=`{:var,0}` in the branch frame.
  @kpair_sigma {:data, :Sigma, [@nat, {:lam, @nat, @nat}], []}
  @kfst {:case, {:global, :kpair}, {:lam, @kpair_sigma, @nat}, [{:mk_pair, 2, {:var, 1}}]}
  @ksnd {:case, {:global, :kpair}, {:lam, @kpair_sigma, @nat}, [{:mk_pair, 2, {:var, 0}}]}

  # {term, expected_nf, note}
  @cases [
    {{:app, {:global, :idnat}, @z}, @z,
     "δ+β: idnat Z → Z (unfold certified global, then β)"},
    {{:app, {:global, :idnat}, {:ctor, :S, [@z]}}, {:ctor, :S, [@z]},
     "δ+β: idnat (S Z) → S Z"},
    {@kfst, @z,
     "δ+ι: fst kpair → Z (unfold to a pair, project first via ι-on-case)"},
    {@ksnd, {:ctor, :S, [@z]},
     "δ+ι: snd kpair → S Z (project second via ι-on-case)"},
    {{:app, {:global, :idnat}, @kfst}, @z,
     "nested: idnat (fst kpair) → Z (two unfolds + a projection)"},
    # idnat's δ-unfold exposes a `snd kpair` case under reduce_unfolded (not the
    # direct unfold_certified_head path the bare case takes) — the post-unfold ι
    # follow-through.
    {{:app, {:global, :idnat}, @ksnd}, {:ctor, :S, [@z]},
     "nested: idnat (snd kpair) → S Z (unfold exposes the case, reduce_unfolded)"}
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
