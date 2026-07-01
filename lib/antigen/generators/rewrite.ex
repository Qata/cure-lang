defmodule Antigen.Generators.Rewrite do
  @moduledoc """
  Known-label `Eq`/`refl`/`rewrite` generator (spec 2026-07-02-antigen-eq-rewrite).
  Each builder hand-constructs a Core def whose `:well_typed`/`:ill_typed` label
  is correct by construction; `Assays.Rewrite` checks the kernel accepts iff
  well-typed. No elaborator, no term generator.
  """
  alias Antigen.Challenge
  alias Cure.Core.{Env, Inductive}

  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}
  @dcoupled {:ctor, :Dcoupled, []}

  # -- shared families (duplicated from Generators.Indexed; those are defp) ----
  defp dec_family,
    do: {Inductive.family(:Dec, [], [], 0),
         [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

  defp foo_family, do: {Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])]}

  # P : Dec -> Type, an empty (constructor-free) index family; `P a` is a valid
  # type whose inhabitants are only ever hypotheses (Pi domains). Used as the
  # rewrite motive family in 4.3/4.4.
  defp p_family, do: {Inductive.family(:P, [], [{:n, @dec}], 0), []}

  @doc "Rebuild the Env: declare every family, then add the def under test."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    env = Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  # -- 4.1 Eq formation -------------------------------------------------------
  @doc """
  Eq-formation obligation. The `Eq` type sits in a Pi domain so check_def's
  type-formation pass exercises `infer({:eq,…})` on its endpoints.
  """
  @spec eq_formation(:well_typed | :ill_typed) :: Challenge.t()
  def eq_formation(:well_typed) do
    eq = {:eq, @dec, @causal, @dcoupled}
    challenge(:well_typed, [dec_family()], :eq_formation,
      {:pi, eq, @dec}, {:lam, eq, @causal},
      "Eq Dec Causal Dcoupled — both endpoints : Dec")
  end

  def eq_formation(:ill_typed) do
    eq = {:eq, @dec, @causal, {:ctor, :MkFoo, []}}
    challenge(:ill_typed, [dec_family(), foo_family()], :eq_formation,
      {:pi, eq, @dec}, {:lam, eq, @causal},
      "ill-typed: Eq Dec Causal MkFoo — MkFoo : Foo, not Dec")
  end

  defp challenge(label, families, name, def_type, def_body, note) do
    Challenge.new(
      kind: :rewrite_eq,
      assay: "rewrite/eq",
      label: label,
      payload: %{families: families, def_name: name, def_type: def_type, def_body: def_body},
      note: note
    )
  end
end
