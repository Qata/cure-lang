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
  @decd {:data, :Dec, [], []}

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

  # -- W4: classic escape hatches (pre-port banking spec §4 W4) ----------------

  @doc """
  Double negation: `MkBad : ((Bad -> Dec) -> Dec) -> Bad`. `Bad` sits two arrow-
  domains deep — positive by naive polarity-flip counting, NEGATIVE for strict
  positivity (any occurrence in an arrow domain is banned). Genuinely unsound to
  admit (Curry-paradox family). Label `:negative`.
  """
  @spec double_negation_family() :: Challenge.t()
  def double_negation_family do
    fam = Inductive.family(:Bad, [], [], 0)
    field = {:pi, {:pi, @bad, @decd}, @decd}
    ctors = [Inductive.ctor(:MkBad, [{:f, field}], [])]

    Challenge.new(
      kind: :family,
      assay: "positivity",
      label: :negative,
      payload: %{family: fam, ctors: ctors},
      note: "W4 double negation: Bad in an arrow domain (two deep) — strict positivity rejects"
    )
  end

  @doc """
  Negative occurrence hidden under a Σ: `MkBad : (Σ (Bad -> Dec). Dec) -> Bad`.
  The arrow-left occurrence of `Bad` sits inside a sigma component. Strict
  positivity must traverse Σ (covariant in both components) and reject. Label
  `:negative`.
  """
  @spec sigma_negative_family() :: Challenge.t()
  def sigma_negative_family do
    fam = Inductive.family(:Bad, [], [], 0)
    field = {:sigma, {:pi, @bad, @decd}, @decd}
    ctors = [Inductive.ctor(:MkBad, [{:f, field}], [])]

    Challenge.new(
      kind: :family,
      assay: "positivity",
      label: :negative,
      payload: %{family: fam, ctors: ctors},
      note: "W4 sigma-hidden negative: Bad left of an arrow inside a Σ component"
    )
  end

  @doc """
  Through-constructor escape: `Box` has `mk : (Bad -> Dec) -> Box`, and
  `Bad` has `MkBad : Box -> Bad` — so `Bad ≅ (Bad -> Dec)` one type layer down.
  Rejecting requires expanding `Box`'s constructor fields during `Bad`'s
  positivity check. Multi-family, so it uses the `:indexed_case` record shape
  (subject family LAST; the def slot is an inert well-typed placeholder — the
  positivity assay ignores it). Label `:negative`.
  """
  @spec through_constructor_negative() :: Challenge.t()
  def through_constructor_negative do
    box = {Inductive.family(:Box, [], [], 0),
           [Inductive.ctor(:mk, [{:f, {:pi, @bad, @decd}}], [])]}

    bad = {Inductive.family(:Bad, [], [], 0),
           [Inductive.ctor(:MkBad, [{:b, {:data, :Box, [], []}}], [])]}

    dec = {Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

    Challenge.new(
      kind: :indexed_case,
      assay: "positivity",
      label: :negative,
      payload: %{
        families: [dec, box, bad],
        def_name: :probe,
        def_type: {:type, 0},
        def_body: {:data, :Dec, [], []}
      },
      note: "W4 through-constructor: Bad -> Dec hidden inside Box's ctor; subject = Bad (last family)"
    )
  end

  @doc "Rebuild the family's `Env` by declaring it."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{family: fam, ctors: ctors}}), do: Inductive.declare(Env.empty(), fam, ctors)
end
