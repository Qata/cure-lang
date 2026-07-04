defmodule Antigen.Generators.BranchUnify do
  @moduledoc """
  Known-label generator for the `branchunify/verdict` vertical
  (`Antigen.Assays.BranchUnify`): direct calls to the public
  `Cure.Core.Kernel.branch_unify/4` (the elaborator's index-refinement delegation)
  over the v1 menu's indexed families, with a correct-by-construction verdict
  (`:trivial` | `:solved` | `:impossible`).

  This drives the kernel's first-order index unifier past what a well-typed `case`
  reaches on its own: every `unify_one` arm, `bind_index` (fresh solve, consistent
  re-bind, and same-key merge conflict), `unify_spine`, `rigid_index?`
  (constructor / data / **`Type`** / int-literal heads), `head_key`, and forced
  equations between two outer index variables — each with a fixed verdict the assay
  checks against the live kernel.
  """
  alias Antigen.{Gen, Challenge}

  # {ctx_vars, dname, cname, index_terms, verdict, note}
  @cases [
    {0, :Vec, :vnil, [{:ctor, :Z, []}], :trivial, "Vec vnil [Z] — syntactic match"},
    {0, :Vec, :vnil, [{:ctor, :S, [{:ctor, :Z, []}]}], :impossible, "Vec vnil [S Z] — rigid Z/S clash"},
    {0, :Vec, :vcons, [{:ctor, :S, [{:ctor, :Z, []}]}], :solved, "Vec vcons [S Z] — bind ctor arg"},
    {1, :Vec, :vcons, [{:var, 0}], :solved, "Vec vcons [outer var] — bind outer index var"},
    {0, :Sq, :mksq, [{:ctor, :Z, []}, {:ctor, :Z, []}], :solved, "Sq mksq [Z,Z] — consistent re-bind"},
    {0, :Sq, :mksq, [{:ctor, :Z, []}, {:ctor, :S, [{:ctor, :Z, []}]}], :impossible, "Sq mksq [Z,S Z] — merge conflict"},
    {2, :Sq, :mksq, [{:var, 0}, {:var, 1}], :solved, "Sq mksq [var0,var1] — forced equation (Solution step)"},
    {0, :Ty, :tnat, [{:type, 0}], :impossible, "Ty tnat [Type0] — rigid data/Type clash"},
    {0, :Tg, :tg0, [{:int_lit, 0}], :trivial, "Tg tg0 [0] — int-literal match"},
    {0, :Tg, :tg0, [{:int_lit, 1}], :trivial, "Tg tg0 [1] — int-literal heads agree (undecided)"},
    # crossing 4-index family: mkcyc : Cyc4 a a b b matched against Cyc4 i j j i
    # induces the multi-key cycle (i:=j then j:=i) → resolve-before-bind collapse.
    {2, :Cyc4, :mkcyc, [{:var, 0}, {:var, 1}, {:var, 1}, {:var, 0}], :solved, "Cyc4 crossing — multi-key cycle collapse"},
    {4, :Cyc4, :mkcyc, [{:var, 0}, {:var, 1}, {:var, 2}, {:var, 3}], :solved, "Cyc4 distinct — 4-index spine solve"}
  ]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@cases), fn {n, d, c, idx, verdict, note} ->
      Gen.return(
        Challenge.new(
          kind: :branch_unify,
          assay: "branchunify/verdict",
          label: verdict,
          payload: %{ctx_vars: n, dname: d, cname: c, indices: idx},
          note: note
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end
