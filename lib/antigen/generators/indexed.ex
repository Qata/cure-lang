defmodule Antigen.Generators.Indexed do
  @moduledoc """
  Known-label indexed-family `case` generator (spec 2026-07-01-antigen-indexed-case).
  Each builder hand-constructs a GADT `case` challenge as raw Core whose
  `:well_typed`/`:ill_typed` label is correct by construction; the assay checks
  the kernel accepts iff well-typed. No elaborator, no term generator.
  """
  alias Antigen.Challenge
  alias Cure.Core.{Env, Inductive}

  @dec {:data, :Dec, [], []}

  # -- shared families --------------------------------------------------------
  defp dec_family, do: {Inductive.family(:Dec, [], [], 0),
                        [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

  defp foo_family, do: {Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])]}

  @doc "Rebuild the Env: declare every family, then add the def under test."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    env = Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  # -- 4.1 branch-family discipline ------------------------------------------
  @doc "Branch-family obligation. `:ill_typed` adds a foreign `Foo` branch to a Dec case."
  @spec branch_family(:well_typed | :ill_typed) :: Challenge.t()
  def branch_family(:well_typed) do
    body =
      {:case, {:ctor, :Causal, []}, {:lam, @dec, @dec},
       [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}

    challenge(:well_typed, [dec_family()], :branch_family, @dec, body,
      "well-typed Dec case, all branches from Dec")
  end

  def branch_family(:ill_typed) do
    body =
      {:case, {:ctor, :Causal, []}, {:lam, @dec, @dec},
       [
         {:Dcoupled, 0, {:ctor, :Causal, []}},
         {:Causal, 0, {:ctor, :Dcoupled, []}},
         {:MkFoo, 0, {:ctor, :Dcoupled, []}}
       ]}

    challenge(:ill_typed, [dec_family(), foo_family()], :branch_family, @dec, body,
      "ill-typed: extra branch names MkFoo, a constructor of family Foo, not Dec")
  end

  # -- 4.2 coverage exactness -------------------------------------------------
  defp tri_family, do: {Inductive.family(:Tri, [], [], 0),
                        [Inductive.ctor(:A, [], []), Inductive.ctor(:B, [], []), Inductive.ctor(:C, [], [])]}

  @tri {:data, :Tri, [], []}

  @doc "Coverage obligation. `:ill_typed` omits a required branch (expects {:error, :coverage})."
  @spec coverage(:well_typed | :ill_typed) :: Challenge.t()
  def coverage(:well_typed) do
    body = {:case, {:ctor, :A, []}, {:lam, @tri, @tri},
            [{:A, 0, {:ctor, :A, []}}, {:B, 0, {:ctor, :A, []}}, {:C, 0, {:ctor, :A, []}}]}
    challenge(:well_typed, [tri_family()], :coverage_gap, @tri, body, "exhaustive Tri case")
  end

  def coverage(:ill_typed) do
    body = {:case, {:ctor, :A, []}, {:lam, @tri, @tri},
            [{:A, 0, {:ctor, :A, []}}, {:B, 0, {:ctor, :A, []}}]}
    challenge(:ill_typed, [tri_family()], :coverage_gap, @tri, body, "non-exhaustive: C omitted")
  end

  defp challenge(label, families, name, def_type, def_body, note) do
    Challenge.new(
      kind: :indexed_case,
      assay: "indexed/case",
      label: label,
      payload: %{families: families, def_name: name, def_type: def_type, def_body: def_body},
      note: note
    )
  end
end
