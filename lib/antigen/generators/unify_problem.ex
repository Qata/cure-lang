defmodule Antigen.Generators.UnifyProblem do
  @moduledoc """
  Fixed catalogs of unification problems for the `Antigen.Assays.Unifier`
  families (spec: antigen-unifier-soundness). Mirrors the elab/normalizer
  fixed-catalog pattern (deterministic, no corpus banking).

    * `elab_soundness_challenges/0` / `elab_intrinsic_challenges/0` — closed
      ctor-only Core terms with metavariables, for `Cure.Elab.Unify` (V2a). All
      terms are closed (no `{:var,_}`) so `Conv.conv?(_,_,[],0,_)` is a valid
      comparison (see spec §3 closedness precondition).
    * `types_fixpoint_challenges/0` / `types_intrinsic_challenges/0` — surface
      types for `Cure.Types.Unify` (V2b). The fixpoint catalog exercises every
      non-syntactic accept the engine has (type-var bind, list/tuple recursion,
      `:int`/`:float` widening in that direction only, named-vs-record match).
  """
  alias Antigen.{Challenge, Gen}
  alias Cure.Elab.MetaCtx

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`) for the two `Cure.Types.Unify`
  assays. `unify_types/fixpoint` enumerates one cell per non-syntactic accept form
  the catalog hand-builds (type-var bind, list/tuple recursion, `:any` LHS,
  int→float widening, named-vs-record); `unify_types/intrinsic` keys on the
  per-entry `expect` branch (`:ok` accept vs the `:error` occurs-check cycle). The
  `Cure.Elab.Unify` (`unify/soundness`, `unify/intrinsic`) catalogs are out of this
  manifest's scope and stay untagged.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    fixpoint =
      for cell <- [:tvar_bind, :list_rec, :tuple_rec, :any_lhs, :int_float_widen, :named_record],
          do: {"unify_types/fixpoint", cell}

    intrinsic = for cell <- [:ok, :error], do: {"unify_types/intrinsic", cell}
    fixpoint ++ intrinsic
  end

  @doc """
  Sampleable generator over the two `Cure.Types.Unify` fixed catalogs (this vertical
  is otherwise a deterministic seed-fed catalog). Used by the coverage-manifest gate
  to confirm every declared cell is actually produced.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of(types_fixpoint_challenges() ++ types_intrinsic_challenges())
  end

  # -- Core term helpers (V2a): closed ctor-only ------------------------------
  defp z0, do: {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}
  defp pair(a, b), do: {:ctor, :Pair, [a, b]}
  defp m(n), do: {:meta, n}

  # -- Surface helper (V2b) ----------------------------------------------------
  defp tv(n), do: {:type_var, n}

  # -- Elab.Unify catalogs (V2a) ----------------------------------------------

  @doc "V2a soundness catalog (closed ctor-only Core terms)."
  @spec elab_soundness_challenges() :: [Challenge.t()]
  def elab_soundness_challenges do
    # {t1, t2, meta_ids}
    [
      {m(0), s(z0()), [0]},
      {pair(m(0), z0()), pair(s(z0()), m(1)), [0, 1]},
      {{:pi, z0(), m(0)}, {:pi, z0(), s(z0())}, [0]},
      # no-metavar reflexive pair — soundness only (NOT intrinsic: meta-closed would be vacuous)
      {s(z0()), s(z0()), []}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{t1, t2, ids}, i} -> elab_ch("unify/soundness", t1, t2, ids, i) end)
  end

  @doc "V2a intrinsic catalog (metavariable-bearing entries only)."
  @spec elab_intrinsic_challenges() :: [Challenge.t()]
  def elab_intrinsic_challenges do
    [
      {m(0), s(z0()), [0]},
      {pair(m(0), z0()), pair(s(z0()), m(1)), [0, 1]},
      {{:pi, z0(), m(0)}, {:pi, z0(), s(z0())}, [0]}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{t1, t2, ids}, i} -> elab_ch("unify/intrinsic", t1, t2, ids, i) end)
  end

  defp elab_ch(assay, t1, t2, meta_ids, seed) do
    Challenge.new(kind: :unify_problem, assay: assay, label: :translatable,
      payload: %{t1: t1, t2: t2, ctx: MetaCtx.new(), sig: nil, meta_ids: meta_ids}, seed: seed)
  end

  # -- Types.Unify catalogs (V2b) ---------------------------------------------

  @doc "V2b fixpoint catalog (surface types, every non-syntactic accept)."
  @spec types_fixpoint_challenges() :: [Challenge.t()]
  def types_fixpoint_challenges do
    [
      {tv("T"), :int, :tvar_bind},
      {{:list, tv("T")}, {:list, :int}, :list_rec},
      {{:tuple, [tv("A"), tv("B")]}, {:tuple, [:int, :string]}, :tuple_rec},
      {:any, tv("T"), :any_lhs},
      {:int, :float, :int_float_widen},
      {{:named, "foo"}, {:record, :foo, []}, :named_record}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{t1, t2, cell}, i} ->
      Challenge.new(kind: :unify_problem, assay: "unify_types/fixpoint", label: :translatable,
        payload: %{t1: t1, t2: t2}, seed: i, cover_tag: cell)
    end)
  end

  @doc "V2b intrinsic catalog (`:ok` entries plus one `:error` cyclic entry)."
  @spec types_intrinsic_challenges() :: [Challenge.t()]
  def types_intrinsic_challenges do
    [
      {tv("T"), :int, :ok},
      {{:list, tv("T")}, {:list, :int}, :ok},
      {{:tuple, [tv("A"), tv("B")]}, {:tuple, [:int, :string]}, :ok},
      {tv("a"), {:list, tv("a")}, :error}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{t1, t2, expect}, i} ->
      Challenge.new(kind: :unify_problem, assay: "unify_types/intrinsic", label: :translatable,
        payload: %{t1: t1, t2: t2, expect: expect}, seed: i, cover_tag: expect)
    end)
  end
end
