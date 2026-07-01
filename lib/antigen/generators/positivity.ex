defmodule Antigen.Generators.Positivity do
  @moduledoc """
  Known-label positivity generator (spec §5.2). Emits `:family` challenges whose
  `:positive` / `:negative` label is correct by construction — cross-checked
  against `Inductive.positive?/2` in the Task-12 self-tests. Family/ctor/binder
  names are a fixed literal set (`:Natp`/`:Zp`/`:Sp`/`:pred`, `:Bad`/`:MkBad`/`:f`)
  so the atoms exist for `:safe` corpus replay (Task 5 safety note).
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.{Env, Inductive}

  @natp {:data, :Natp, [], []}
  @bad {:data, :Bad, [], []}

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.frequency([
      {1, Gen.return(positive_family())},
      {1, Gen.return(negative_family())}
    ])
  end

  @doc "A strictly-positive Nat-like family: the recursive occurrence in `Sp` is a direct argument (positive position)."
  @spec positive_family() :: Challenge.t()
  def positive_family do
    fam = Inductive.family(:Natp, [], [], 0)
    ctors = [Inductive.ctor(:Zp, [], []), Inductive.ctor(:Sp, [{:pred, @natp}], [])]

    Challenge.new(
      kind: :family,
      assay: "positivity",
      label: :positive,
      payload: %{family: fam, ctors: ctors},
      note: "strictly-positive Nat-like family"
    )
  end

  @doc "A non-strictly-positive family: `MkBad` takes `Bad -> Bad`, so `Bad` occurs left of an arrow (negative)."
  @spec negative_family() :: Challenge.t()
  def negative_family do
    fam = Inductive.family(:Bad, [], [], 0)
    ctors = [Inductive.ctor(:MkBad, [{:f, {:pi, @bad, @bad}}], [])]

    Challenge.new(
      kind: :family,
      assay: "positivity",
      label: :negative,
      payload: %{family: fam, ctors: ctors},
      note: "negative occurrence: Bad left of an arrow"
    )
  end

  @doc "Rebuild the family's `Env` by declaring it."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{family: fam, ctors: ctors}}), do: Inductive.declare(Env.empty(), fam, ctors)
end
