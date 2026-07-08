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
      {2, Gen.return(positive_family())},
      {2, Gen.return(negative_family())},
      # Richer single-family negatives — Σ traversal + nested arrows.
      {1, Gen.return(double_negation_family())},
      {1, Gen.return(sigma_negative_family())},
      # Multi-family through-constructor shapes — the only inputs that reach the
      # deep positivity branches (strictly_positive? through-family 316-335,
      # occurs_deep? 342-348, data_heads/gather_data_heads). Both polarities.
      {1, Gen.return(through_constructor_positive())},
      {1, Gen.return(through_constructor_negative())},
      {1, Gen.return(deep_negative_family())},
      # PARAMETRIC single-family generation (not curated): a random family whose
      # strict-positivity LABEL is correct by construction — every ctor-arg type
      # is drawn from a positivity-safe grammar for `:positive`, or one arg is
      # forced into an arrow domain for `:negative`. Genuine sampling over an
      # unbounded (Π/Σ-nested) family-shape space, cross-checked against the real
      # `Inductive.positive?` oracle in the generator soundness test.
      {4, parametric_family()},
      # occurs?/2 recursion coverage: strictly-positive families whose ctor field
      # is `Π <dom>. Nat` with <dom> exercising one occurs?/2 term-shape clause
      # (the arrow domain is scanned by occurs_deep? → occurs?). The subject never
      # occurs in <dom>, so the label stays :positive (correct by construction).
      {3, occurs_family()},
      # NEGATIVE: subject in a data type's INDEX position → strictly_positive?'s
      # occurs-in-params/indices branch (318 → 319) fires → not strictly positive.
      {2, Gen.return(occurs_in_index_family())}
    ])
  end

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  # Subject family — defined here (module top) so every generator below reads it;
  # module attributes resolve at the textual point of use, so a definition further
  # down would read nil in the occurs?/2 generators.
  @pgen {:data, :Pgen, [], []}

  # Arrow domains, one per occurs?/2 recursion clause (lam/sigma/pair/app/fst/snd/
  # ctor/data/case + a non-term leaf for the fallback). The former eq/refl/rewrite
  # entries retired with the primitive identity forms (Phase C); their walker
  # arms are covered by the inductive spellings below (Equivalent :data,
  # reflexive :ctor, and the single-branch :case transport shape). None mention
  # :Pgen, so every family that carries them stays strictly positive.
  @occurs_domains [
    {:lam, @nat, @z},
    {:sigma, @z, @z},
    {:pair, @z, @z},
    {:app, @z, @z},
    {:fst, @z},
    {:snd, @z},
    {:ctor, :S, [@z]},
    {:data, :Equivalent, [@nat], [@z, @z]},
    {:ctor, :reflexive, [@z]},
    {:case, {:ctor, :reflexive, [@z]}, @z, [{:reflexive, 1, @z}]},
    {:case, @z, @z, [{:PC0, 0, @z}]},
    {:app, {:int_lit, 0}, {:int_lit, 0}}
  ]

  # A non-strictly-positive :Pgen family whose ctor field is `Vec Pgen` — the
  # subject sits in an index position of another data type, so strictly_positive?'s
  # data-other branch takes its occurs-in-params/indices path (318 → 319 false).
  # Correct label :negative (positive? rejects), cross-checked in the test.
  defp occurs_in_index_family do
    parametric_challenge(
      [[{:data, :Vec, [], [@pgen]}]],
      :negative,
      "occurs?/2 in a data index: subject in an index position (strictly_positive? 318)"
    )
  end

  # Strictly-positive :Pgen families packing SIX arrow-domain shapes each (2 ctors
  # × 3 `Π <dom>. <cod>` fields), split into two groups so every occurs?/2 clause
  # is reliably hit each run despite the generator mix diluting single draws. The
  # codomain alternates Nat / Int, covering strictly_positive?'s data-other index
  # scan (318, Nat cod) and its non-Π/Σ/data fallback (335, Int cod). Positive by
  # construction (the subject never occurs in a domain), cross-checked in the test.
  defp occurs_family do
    groups = [Enum.take(@occurs_domains, 6), Enum.drop(@occurs_domains, 6)]

    Gen.bind(Gen.member_of(groups), fn group ->
      fields =
        group
        |> Enum.with_index()
        |> Enum.map(fn {dom, i} ->
          cod = if rem(i, 2) == 0, do: @nat, else: {:int_type}
          {:pi, dom, cod}
        end)

      Gen.return(
        parametric_challenge(
          Enum.chunk_every(fields, 3),
          :positive,
          "occurs?/2 coverage (packed): 6 arrow-domain shapes"
        )
      )
    end)
  end

  # -- parametric family generation (correct-by-construction labels) ----------

  # Fixed name pool (finite → the atoms stay in Challenge.@known_atoms for :safe
  # replay). One subject family `:Pgen` (defined at module top), ≤2 ctors, ≤3 arg
  # binders per ctor.
  @bases [{:data, :Nat, [], []}, {:data, :Bd, [], []}]
  @ctor_names {:PC0, :PC1}
  @binder_names {:pq0, :pq1, :pq2}
  @gen_depth 2

  @doc "A random family with a correct-by-construction strict-positivity label."
  @spec parametric_family() :: Gen.t()
  def parametric_family do
    Gen.frequency([{1, positive_parametric()}, {1, negative_parametric()}])
  end

  # POSITIVE: every ctor arg is positivity-safe (subject never left of an arrow),
  # so `Inductive.positive?` accepts by construction.
  defp positive_parametric do
    Gen.bind(Gen.int(1, 2), fn n_ctors ->
      Gen.bind(gen_list_n(n_ctors, gen_safe_args(@gen_depth)), fn arg_lists ->
        Gen.return(parametric_challenge(arg_lists, :positive, "parametric strictly-positive family"))
      end)
    end)
  end

  # NEGATIVE: identical skeleton, but one extra arg on the first ctor places the
  # subject in an arrow domain → `positive?` rejects by construction.
  defp negative_parametric do
    Gen.bind(Gen.int(1, 2), fn n_ctors ->
      Gen.bind(gen_list_n(n_ctors, gen_safe_args(@gen_depth)), fn arg_lists ->
        Gen.bind(negative_arg(@gen_depth), fn neg ->
          [first | rest] = arg_lists
          Gen.return(parametric_challenge([first ++ [neg] | rest], :negative,
            "parametric non-strictly-positive family (subject left of an arrow)"))
        end)
      end)
    end)
  end

  defp parametric_challenge(arg_type_lists, label, note) do
    ctors =
      arg_type_lists
      |> Enum.with_index()
      |> Enum.map(fn {arg_types, ci} ->
        args =
          arg_types
          |> Enum.with_index()
          |> Enum.map(fn {ty, ai} -> {elem(@binder_names, ai), ty} end)

        Inductive.ctor(elem(@ctor_names, ci), args, [])
      end)

    Challenge.new(
      kind: :family,
      assay: "positivity",
      label: label,
      payload: %{family: Inductive.family(:Pgen, [], [], 0), ctors: ctors},
      note: note
    )
  end

  # A ctor's argument telescope: 0-2 positivity-safe types.
  defp gen_safe_args(depth) do
    Gen.frequency([
      {1, Gen.return([])},
      {2, gen_list_n(1, positive_safe(depth))},
      {2, gen_list_n(2, positive_safe(depth))}
    ])
  end

  # A positivity-SAFE type: the subject `:Pgen` may appear only strictly
  # positively — directly, in a Σ component, or in an arrow CODOMAIN; never in an
  # arrow domain (which is F-free: a base type).
  defp positive_safe(0), do: Gen.frequency([{2, Gen.member_of(@bases)}, {1, Gen.return(@pgen)}])

  defp positive_safe(depth) do
    Gen.frequency([
      {3, Gen.member_of(@bases)},
      {2, Gen.return(@pgen)},
      {1, Gen.bind(Gen.member_of(@bases), fn dom ->
            Gen.bind(positive_safe(depth - 1), fn cod -> Gen.return({:pi, dom, cod}) end)
          end)},
      {1, Gen.bind(positive_safe(depth - 1), fn a ->
            Gen.bind(positive_safe(depth - 1), fn b -> Gen.return({:sigma, a, b}) end)
          end)}
    ])
  end

  # A NEGATIVE-position arg: the subject appears somewhere in an arrow DOMAIN,
  # which strict positivity always rejects (every option is provably negative).
  defp negative_arg(depth) do
    Gen.frequency([
      {2, Gen.bind(positive_safe(depth), fn cod -> Gen.return({:pi, @pgen, cod}) end)},
      {1, Gen.bind(positive_safe(depth), fn cod ->
            Gen.return({:pi, {:sigma, @pgen, hd(@bases)}, cod})
          end)},
      {1, Gen.return({:pi, {:pi, hd(@bases), @pgen}, hd(@bases)})}
    ])
  end

  # Sequence `n` independent draws of `g` into a list.
  defp gen_list_n(0, _g), do: Gen.return([])

  defp gen_list_n(n, g) do
    Gen.bind(g, fn x -> Gen.bind(gen_list_n(n - 1, g), fn rest -> Gen.return([x | rest]) end) end)
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

  @doc """
  Through-constructor POSITIVE: `MkT : Wrap -> T`, and `wrap : T -> Wrap`, so `T`
  occurs strictly-positively one family layer down. Accepting requires expanding
  `Wrap`'s constructor fields during `T`'s check and confirming the occurrence is
  positive — the accept-path twin of `through_constructor_negative` (verified
  `:ok` by `Inductive.positive?`). Multi-family (`:indexed_case`). Label `:positive`.
  """
  @spec through_constructor_positive() :: Challenge.t()
  def through_constructor_positive do
    wrap = {Inductive.family(:Wrap, [], [], 0),
            [Inductive.ctor(:wrap, [{:x, {:data, :T, [], []}}], [])]}

    t = {Inductive.family(:T, [], [], 0),
         [Inductive.ctor(:MkT, [{:b, {:data, :Wrap, [], []}}], [])]}

    Challenge.new(
      kind: :indexed_case,
      assay: "positivity",
      label: :positive,
      payload: %{families: [wrap, t], def_name: :probe, def_type: {:type, 0}, def_body: {:data, :T, [], []}},
      note: "through-constructor positive: T strictly-positive inside Wrap's ctor; subject = T (last family)"
    )
  end

  @doc """
  Through-constructor DEEP negative: `MkBad : (Wrap -> Dec) -> Bad`, and
  `wrap : Bad -> Wrap`. `Bad` is NOT in the arrow domain directly (`Wrap` is) —
  it is reachable only *through* `Wrap`'s constructor field, so rejecting exercises
  `occurs_deep?`'s through-family loop (and `data_heads`/`gather_data_heads`),
  which the direct-occurrence negatives never reach. Verified `{:error, …}` by
  `Inductive.positive?`. Multi-family (`:indexed_case`). Label `:negative`.
  """
  @spec deep_negative_family() :: Challenge.t()
  def deep_negative_family do
    dec = {Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

    wrap = {Inductive.family(:Wrap, [], [], 0),
            [Inductive.ctor(:wrap, [{:x, {:data, :Bad, [], []}}], [])]}

    bad = {Inductive.family(:Bad, [], [], 0),
           [Inductive.ctor(:MkBad, [{:f, {:pi, {:data, :Wrap, [], []}, {:data, :Dec, [], []}}}], [])]}

    Challenge.new(
      kind: :indexed_case,
      assay: "positivity",
      label: :negative,
      payload: %{families: [dec, wrap, bad], def_name: :probe, def_type: {:type, 0}, def_body: {:data, :Dec, [], []}},
      note: "through-constructor deep negative: Bad reachable only via Wrap's ctor in an arrow domain (occurs_deep?); subject = Bad (last family)"
    )
  end

  @doc "Rebuild the family's `Env` by declaring it (single-family or multi-family payload)."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{family: fam, ctors: ctors}}), do: Inductive.declare(Env.empty(), fam, ctors)

  def env_of(%Challenge{payload: %{families: families}}) do
    Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
  end
end
