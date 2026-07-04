defmodule Antigen.Generators.IndexedDecl do
  @moduledoc """
  Parametric generator for **indexed-family declaration checking** — the
  `Kernel.check_ctor` → `check_result_indices` path, which validates that a
  constructor's result indices match the family's index telescope in count and
  type. Distinct from `Generators.DepMatch`, which drives index unification at
  case-MATCH time; this drives index checking at DECLARE time (no live generator
  reached it before — the universes `:family` probes were all non-indexed).

  Emits `:family` universes challenges (assay `"universes"`, oracle = known label)
  for `IdxI : (n:<T>) -> Type0` where `T` is a builtin literal type (Int or Float),
  so the single-family challenge needs no auxiliary declarations:

    * **well_typed** — `mki : IdxI <lit>` with a matching-type literal index; the
      sole driver of check_result_indices' success path (991-true / 992 / 993).
    * **ill_typed (type)** — `mkb : IdxI <lit>` with a wrong-type literal index →
      `conversion_failure` (992 / 994).
    * **ill_typed (arity)** — result index of the wrong count (0 or 2 vs a 1-index
      telescope) → `:index_arity` (991-false).

  Both the value and the index type vary parametrically; the known label is correct
  by construction and cross-checked against the kernel in the generator's test.
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Inductive

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of([:int, :float]), fn kind ->
      Gen.bind(variant(kind), fn {label, ctors} ->
        fam = Inductive.family(:IdxI, [], [{:n, itype(kind)}], 0)

        Gen.return(
          Challenge.new(
            kind: :family,
            assay: "universes",
            label: label,
            payload: %{family: fam, ctors: ctors},
            note: "indexed-decl check_result_indices: IdxI (n:#{kind}), #{label}"
          )
        )
      end)
    end)
  end

  defp itype(:int), do: {:int_type}
  defp itype(:float), do: {:float_type}

  defp variant(kind) do
    Gen.frequency([
      # matching-type literal index → accepted (success path)
      {3, mk(:well_typed, :mki, single(lit(kind)))},
      # mismatched-type literal index → conversion_failure
      {2, mk(:ill_typed, :mkb, single(lit(other(kind))))},
      # wrong result-index arity vs the 1-index telescope → :index_arity
      {1, mk(:ill_typed, :mkb, arity_indices(kind))}
    ])
  end

  defp mk(label, cname, indices_gen) do
    Gen.bind(indices_gen, fn is -> Gen.return({label, [Inductive.ctor(cname, [], is)]}) end)
  end

  defp single(lit_gen), do: Gen.bind(lit_gen, fn v -> Gen.return([v]) end)

  # 0 or 2 matching-type indices (both wrong against the single-index telescope)
  defp arity_indices(kind) do
    Gen.frequency([
      {1, Gen.return([])},
      {1, Gen.bind(lit(kind), fn a -> Gen.bind(lit(kind), fn b -> Gen.return([a, b]) end) end)}
    ])
  end

  defp other(:int), do: :float
  defp other(:float), do: :int

  defp lit(:int), do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end)
  defp lit(:float), do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
end
