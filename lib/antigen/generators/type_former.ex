defmodule Antigen.Generators.TypeFormer do
  @moduledoc """
  Structure-directed generator for **type-former** terms used in type position —
  universes `{:type, N}`, dependent function/pair types `{:pi, A, B}` /
  `{:sigma, A, B}`, and indexed data types `Vec n`. The ordinary value-term
  generators build INHABITANTS, not the type-formers themselves, so these
  exercise `infer`'s and (measured) `Normalise`'s type-former paths (nf of Π/Σ/
  data/universe terms).

  NOTE (honest scope): this does NOT reach `Kernel.infer_type_value_sort/2` — that
  function is called only from `check_motive_wf` (a `case`'s motive), so hitting
  it needs a dependent-`case` whose motive is a type-former, not a bare type-
  former in inferring position. That is the dependent-matching lever, tracked
  separately.

  Every term is a well-formed **type** over the v1 signature in the empty context;
  its claimed `type` is the exact universe `infer` returns (verified in the
  soundness test). Tagged for `term/infer_check`.
  """
  alias Antigen.{Gen, Challenge}

  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  # Base types, all of sort Type 0 — used as Π/Σ components so the former is Type 0.
  @small_types [{:int_type}, {:float_type}, @nat, @bd]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(former(), fn {term, type} ->
      Gen.return(
        Challenge.new(
          kind: :typed_term,
          assay: "term/infer_check",
          label: :well_typed,
          payload: %{sig: :v1, ctx: [], type: type, term: term},
          note: "type former"
        )
      )
    end)
  end

  # {term, its universe} — the claimed type is always a {:type, _}.
  defp former do
    Gen.frequency([
      # a bare universe: Type N : Type (N+1). Capped at N=1 — the kernel's
      # universe ceiling rejects Type 2's sort (Type 3).
      {2, Gen.bind(Gen.int(0, 1), fn n -> Gen.return({{:type, n}, {:type, n + 1}}) end)},
      # Π/Σ over base types → Type 0
      {3, Gen.bind(small(), fn a -> Gen.bind(small(), fn b -> Gen.return({{:pi, a, b}, {:type, 0}}) end) end)},
      {3, Gen.bind(small(), fn a -> Gen.bind(small(), fn b -> Gen.return({{:sigma, a, b}, {:type, 0}}) end) end)},
      # dependent Π with a universe codomain → Type 1
      {2, Gen.bind(small(), fn a -> Gen.return({{:pi, a, {:type, 0}}, {:type, 1}}) end)},
      # indexed data type Vec n → Type 0
      {2, Gen.bind(nat_numeral(), fn n -> Gen.return({{:data, :Vec, [], [n]}, {:type, 0}}) end)},
      # a bare base type in type position (Int/Float/Nat/Bd) → Type 0
      {1, Gen.bind(small(), fn a -> Gen.return({a, {:type, 0}}) end)}
    ])
  end

  defp small, do: Gen.member_of(@small_types)

  defp nat_numeral do
    Gen.bind(Gen.int(0, 4), fn n ->
      Gen.return(Enum.reduce(1..n//1, {:ctor, :Z, []}, fn _, acc -> {:ctor, :S, [acc]} end))
    end)
  end
end
