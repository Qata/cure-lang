defmodule Antigen.Generators.CheckMode do
  @moduledoc """
  Known-label generator for the `check/verdict` vertical
  (`Antigen.Assays.CheckMode`): direct calls to `Cure.Core.Kernel.check/3` with a
  correct-by-construction verdict (`:accept` | `:reject`).

  Checking mode is the kernel path pure inference cannot reach on its own — a
  parameter-bearing constructor (`Cons`/`Nil : List A`, whose family parameter `A`
  only the EXPECTED type supplies), a hole accepted at any goal type, and the
  Σ-introduction rule whose second component is checked against the first's
  substituted codomain. The infer-first `term/*` assays never exercise these
  (they infer, then check against the inferred type); this vertical drives
  `check/3` head-on with a known accept/reject verdict the assay confirms against
  the live kernel.
  """
  alias Antigen.{Gen, Challenge}

  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  @z {:ctor, :Z, []}
  @nilc {:ctor, :Nil, []}
  @cons {:ctor, :Cons, [{:ctor, :Z, []}, {:ctor, :Nil, []}]}
  @list_nat {:data, :List, [{:data, :Nat, [], []}], []}

  # {ctx_vars, term, type_term, verdict, note}
  @cases [
    {0, @cons, @list_nat, :accept,
     "check Cons Z Nil : List Nat — parameter-bearing ctor (checking mode)"},
    {0, @nilc, @list_nat, :accept,
     "check Nil : List Nat — nullary parameter-bearing ctor"},
    {0, {:hole, "h"}, @list_nat, :accept,
     "check hole : List Nat — a hole is accepted at any goal type"},
    {0, {:pair, @z, @z}, {:sigma, @nat, @nat}, :accept,
     "check (Z, Z) : Σ Nat. Nat — Σ-introduction, second component ok"},
    {0, {:pair, @z, {:ctor, :T, []}}, {:sigma, @nat, @nat}, :reject,
     "check (Z, T) : Σ Nat. Nat — second component Bd ≠ Nat (sigma_mismatch)"},
    {0, @cons, {:data, :List, [@bd], []}, :reject,
     "check Cons Z Nil : List Bd — element Z:Nat clashes the family param Bd (index_mismatch)"},
    {0, {:ctor, :nosuchctor, []}, @list_nat, :reject,
     "check nosuchctor : List Nat — checking-mode unknown constructor (unknown_ctor)"}
  ]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@cases), fn {n, term, ty, verdict, note} ->
      Gen.return(
        Challenge.new(
          kind: :check_mode,
          assay: "check/verdict",
          label: verdict,
          payload: %{ctx_vars: n, term: term, type: ty},
          note: note
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end
