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

  # -- 4.2 refl typing + reflexive-conversion guard ---------------------------
  @spec refl_typing(:base | :redex | :conjunct1_violation | :conjunct2_violation) :: Challenge.t()
  # base: refl Causal : Eq Dec Causal Causal, in a def that checks the refl.
  def refl_typing(:base) do
    eq = {:eq, @dec, @causal, @causal}
    challenge(:well_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "refl Causal : Eq Dec Causal Causal")
  end

  # redex: endpoint is a redex that normalizes to Causal — conv is up-to-nf.
  # (λx:Dec. x) Causal ≡ Causal, so refl Causal : Eq Dec Causal ((λx.x) Causal).
  def refl_typing(:redex) do
    redex = {:app, {:lam, @dec, {:var, 0}}, @causal}
    eq = {:eq, @dec, @causal, redex}
    challenge(:well_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "refl Causal against Eq Dec Causal ((λx.x) Causal) — conv up-to-normalization")
  end

  # conjunct-1 violation: endpoints not convertible (Causal vs Dcoupled), a = Causal.
  def refl_typing(:conjunct1_violation) do
    eq = {:eq, @dec, @causal, @dcoupled}
    challenge(:ill_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "ill-typed: refl Causal : Eq Dec Causal Dcoupled — endpoints not convertible (conjunct 1)")
  end

  # conjunct-2 violation: endpoints equal to each other (Dcoupled,Dcoupled) so
  # conjunct 1 holds, but refl's subject `a`=Causal is not convertible to them.
  def refl_typing(:conjunct2_violation) do
    eq = {:eq, @dec, @dcoupled, @dcoupled}
    challenge(:ill_typed, [dec_family()], :refl_typing, eq, {:refl, @causal},
      "ill-typed: refl Causal : Eq Dec Dcoupled Dcoupled — conjunct 1 holds, subject≠endpoints (conjunct 2)")
  end

  # -- 4.3 rewrite premise discipline -----------------------------------------
  # Motive M = λx:Dec. P x; the equality proof is a hypothesis p : Eq Dec Causal
  # Dcoupled (Causal≠Dcoupled has no ground proof, so it must be assumed). de
  # Bruijn under `[p, h]`: `h`=var0, `p`=var1.
  @p_causal {:data, :P, [], [{:ctor, :Causal, []}]}
  @p_dcoupled {:data, :P, [], [{:ctor, :Dcoupled, []}]}
  @motive {:lam, @dec, {:data, :P, [], [{:var, 0}]}}
  @eq_cd {:eq, @dec, {:ctor, :Causal, []}, {:ctor, :Dcoupled, []}}

  @spec rewrite_premise(:well_typed | :proof_not_eq | :body_mismatch) :: Challenge.t()
  # def : Π(p:Eq Dec Causal Dcoupled). Π(h:P Causal). P Dcoupled
  #     = λp.λh. rewrite p (λx.P x) h
  def rewrite_premise(:well_typed) do
    dt = {:pi, @eq_cd, {:pi, @p_causal, @p_dcoupled}}
    body = {:lam, @eq_cd, {:lam, @p_causal, {:rewrite, {:var, 1}, @motive, {:var, 0}}}}
    challenge(:well_typed, [dec_family(), p_family()], :rewrite_premise, dt, body,
      "rewrite p (λx.P x) h : P Dcoupled from h : P Causal")
  end

  # proof is `h : P Causal`, not an equality → ensure_eq rejects.
  def rewrite_premise(:proof_not_eq) do
    dt = {:pi, @p_causal, @p_causal}
    body = {:lam, @p_causal, {:rewrite, {:var, 0}, @motive, {:var, 0}}}
    challenge(:ill_typed, [dec_family(), p_family()], :rewrite_premise, dt, body,
      "ill-typed: rewrite proof is h : P Causal, not an equality")
  end

  # proof IS a genuine equality (so we reach the body check), but the body
  # `Causal : Dec` does not check at M a = P Causal → :rewrite_premise.
  def rewrite_premise(:body_mismatch) do
    dt = {:pi, @eq_cd, @p_dcoupled}
    body = {:lam, @eq_cd, {:rewrite, {:var, 0}, @motive, {:ctor, :Causal, []}}}
    challenge(:ill_typed, [dec_family(), p_family()], :rewrite_premise, dt, body,
      "ill-typed: rewrite body Causal:Dec, not P Causal → :rewrite_premise")
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
