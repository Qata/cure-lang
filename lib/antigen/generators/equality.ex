defmodule Antigen.Generators.Equality do
  @moduledoc """
  Structure-directed generator for the **propositional-equality fragment** —
  `{:refl, a}`, `{:eq, ty, a, b}` (the `Eq` type former as a `Type 0`
  proposition), and `{:rewrite, proof, motive, body}`. This is the reachability
  lever for the kernel's equality paths, which the mode-directed `Generators.Term`
  never emits (its goal menu has no `Eq` type): `Kernel.infer`'s eq/refl/rewrite
  clauses + `infer_type_value_sort` (Eq type-formation) + `ensure_eq`, `Eval`'s
  eq/refl/rewrite evaluation, `Serialize`'s eq/refl/rewrite encode+decode, and
  `Quote`'s `veq`/`vrefl` reification.

  Every term is well-typed **by construction** over the v1 signature in the empty
  context: operands are closed inhabitants of the numeric / menu-datatype menu,
  and the claimed `type` is exactly what `infer` returns (verified in the
  generator's soundness test):

    * `refl a`                → `Eq ty a a`
    * `Eq ty a b`            → `Type 0`
    * `rewrite (refl a) (λ_. Nat) n` → `Nat`  (constant motive, `n : Nat`)
  """
  alias Antigen.{Gen, Challenge}

  @assays ["term/infer_check", "term/subject_reduction", "term/normalization"]
  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  @bool {:data, :Bool, [], []}

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@assays), fn assay ->
      Gen.bind(eq_term(), fn {term, type} ->
        Gen.return(
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: type, term: term},
            note: "propositional equality"
          )
        )
      end)
    end)
  end

  # -- term + its inferred type ----------------------------------------------
  defp eq_term do
    Gen.frequency([
      {3, refl_term()},
      {3, eq_type_term()},
      {2, rewrite_term()}
    ])
  end

  # refl a : Eq ty a a
  defp refl_term do
    Gen.bind(inhabitant(), fn {a, ty} -> Gen.return({{:refl, a}, {:eq, ty, a, a}}) end)
  end

  # Eq ty a b : Type 0  (a, b share the same type ty — a well-typed proposition,
  # true or false)
  defp eq_type_term do
    Gen.bind(typed_pair(), fn {a, b, ty} ->
      Gen.return({{:eq, ty, a, b}, {:type, 0}})
    end)
  end

  # rewrite (refl a) at (λ_. Nat) in n : Nat  — constant motive, refl proof.
  defp rewrite_term do
    Gen.bind(inhabitant(), fn {a, ty} ->
      Gen.bind(nat_numeral(), fn n ->
        {{:rewrite, {:refl, a}, {:lam, ty, @nat}, n}, @nat}
        |> Gen.return()
      end)
    end)
  end

  # -- closed inhabitants paired with their type ------------------------------
  defp inhabitant do
    Gen.frequency([
      {3, Gen.bind(nat_numeral(), fn n -> Gen.return({n, @nat}) end)},
      {2, Gen.bind(int_lit(), fn n -> Gen.return({n, {:int_type}}) end)},
      {2, Gen.bind(float_lit(), fn f -> Gen.return({f, {:float_type}}) end)},
      {1, Gen.bind(Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}]), fn t -> Gen.return({t, @bd}) end)},
      {1, Gen.bind(Gen.member_of([{:ctor, :False, []}, {:ctor, :True, []}]), fn t -> Gen.return({t, @bool}) end)}
    ])
  end

  # Two inhabitants of the SAME type (for a well-formed Eq proposition).
  defp typed_pair do
    Gen.frequency([
      {3, both(nat_numeral(), @nat)},
      {2, both(int_lit(), {:int_type})},
      {2, both(float_lit(), {:float_type})},
      {1, both(Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}]), @bd)},
      {1, both(Gen.member_of([{:ctor, :False, []}, {:ctor, :True, []}]), @bool)}
    ])
  end

  defp both(value_gen, ty) do
    Gen.bind(value_gen, fn a -> Gen.bind(value_gen, fn b -> Gen.return({a, b, ty}) end) end)
  end

  # -- leaf value generators --------------------------------------------------
  defp nat_numeral do
    Gen.bind(Gen.int(0, 4), fn n ->
      Gen.return(Enum.reduce(1..n//1, {:ctor, :Z, []}, fn _, acc -> {:ctor, :S, [acc]} end))
    end)
  end

  defp int_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end)
  defp float_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
end
