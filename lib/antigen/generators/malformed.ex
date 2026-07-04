defmodule Antigen.Generators.Malformed do
  @moduledoc """
  Parametric generator for the NEGATIVE `term/rejection` vertical (assay
  `Antigen.Assays.Malformed`): terms that `Kernel.infer` MUST reject, exercising
  its defensive rejection clauses that no well-typed generator reaches. Each
  challenge is closed (empty local context over the v1 menu) and labelled
  `:ill_typed`; the assay confirms the kernel rejects it.

  Malformation families (each parametric over its variable positions):

    * `{:absurd}` in a reachable position → `:absurd_in_reachable_position`
    * `{:global, <undeclared>}` → `:unknown_global`
    * `{:data, <undeclared>, …}` → `{:unknown_family, _}`
    * `{:ctor, <undeclared>, …}` → `{:unknown_ctor, _}`
    * `case <non-data>` → `:case_scrutinee_not_data` (scrutinee is a literal /
      universe / Π-type / λ, none of which infer to a data value)
    * `<non-function> arg` → `ensure_pi` guard
    * `rewrite <non-Eq proof>` → `ensure_eq` guard
  """
  alias Antigen.{Gen, Challenge}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(malformation(), fn {term, note} ->
      Gen.return(
        Challenge.new(
          kind: :malformed,
          assay: "term/rejection",
          label: :ill_typed,
          payload: %{sig: :v1, ctx: [], term: term},
          note: "malformed (must reject): #{note}"
        )
      )
    end)
  end

  defp malformation do
    Gen.frequency([
      {2, tagged({:absurd}, "absurd in reachable position")},
      {2, tagged({:global, :nosuchdef}, "unknown global")},
      {2, tagged({:data, :NoSuchFamily, [], []}, "unknown family")},
      {2, ctor_bad()},
      {3, case_non_data()},
      {2, app_non_function()},
      {2, rewrite_bad_proof()}
    ])
  end

  # {:ctor, <undeclared>, args} with a random (well-formed) argument list.
  defp ctor_bad do
    Gen.bind(arglist(), fn args -> tagged({:ctor, :nosuchctor, args}, "unknown ctor") end)
  end

  # case over a scrutinee that does NOT infer to a data value.
  defp case_non_data do
    Gen.bind(non_data(), fn scrut ->
      tagged({:case, scrut, {:lam, @nat, @nat}, []}, "case scrutinee not data")
    end)
  end

  # apply a non-function to an argument.
  defp app_non_function do
    Gen.bind(non_function(), fn f -> tagged({:app, f, @z}, "apply non-function") end)
  end

  # rewrite whose proof does not infer to an equality type.
  defp rewrite_bad_proof do
    Gen.bind(non_eq_proof(), fn pr ->
      tagged({:rewrite, pr, {:lam, @nat, @nat}, @z}, "rewrite proof not an equality")
    end)
  end

  # --- parametric leaf pools -------------------------------------------------

  # values / types that are NOT data values (so `case` over them is not_data)
  defp non_data do
    Gen.one_of([
      literal(),
      Gen.return({:type, 0}),
      Gen.return({:pi, @nat, @nat}),
      Gen.return({:lam, @nat, @z})
    ])
  end

  # terms that do NOT infer to a Π type (so applying them trips ensure_pi)
  defp non_function do
    Gen.one_of([literal(), Gen.return(@z), Gen.return({:type, 0})])
  end

  # terms that do NOT infer to an Eq type (so rewrite trips ensure_eq)
  defp non_eq_proof, do: Gen.one_of([literal(), Gen.return(@z)])

  defp literal do
    Gen.one_of([
      Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end),
      Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
    ])
  end

  # a short list of well-formed argument terms (for the unknown-ctor case)
  defp arglist do
    Gen.frequency([
      {2, Gen.return([])},
      {1, Gen.return([@z])},
      {1, Gen.return([@z, @z])}
    ])
  end

  defp tagged(term, note), do: Gen.return({term, note})
end
