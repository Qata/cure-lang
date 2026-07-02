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
  @wr {:data, :Wr, [], []}
  # SNat(s): an INDEXED family (one Dec index) — used as a Π DOMAIN inside a motive
  # (the convoy encoding of `with` sibling refinement). `s` = the motive/def binder.
  @snat_s {:data, :SNat, [], [{:var, 0}]}

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

  # -- 4.3 compound-index refinement (crown jewel) ----------------------------
  defp ix_family, do: {Inductive.family(:Ix, [], [{:n, @dec}], 0),
                       [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])]}

  @doc """
  Compound-index refinement obligation. The `wrap` ctor's result index is the
  GROUND term `Causal` (not a bare var), so `branch_index_subst` drops the
  refinement equation.
  """
  @spec refinement(:well_typed | :ill_typed) :: Challenge.t()
  def refinement(:well_typed) do
    # Refinement-complete but genuinely legal: `h`, bound before the case at the
    # unrefined type `Ix n`, is reused in the `wrap` branch where the required
    # type is `Ix Causal`. Only the dropped ground-index equation (n := Causal)
    # bridges them. A sound, refinement-complete kernel accepts this by refining
    # h's context type; the current kernel drops the equation and is expected to
    # reject (incompleteness, reported not fixed).
    ix_of_0 = {:data, :Ix, [], [{:var, 0}]}
    ix_of_1 = {:data, :Ix, [], [{:var, 1}]}
    ix_of_2 = {:data, :Ix, [], [{:var, 2}]}

    def_type = {:pi, @dec, {:pi, ix_of_0, {:pi, ix_of_1, ix_of_2}}}
    motive = {:lam, @dec, {:lam, ix_of_0, ix_of_1}}
    body = {:lam, @dec, {:lam, ix_of_0, {:lam, ix_of_1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}

    challenge(:well_typed, [dec_family(), ix_family()], :refine, def_type, body,
      "refinement-complete: reusing h : Ix n as Ix Causal in the wrap branch needs n:=Causal")
  end

  def refinement(:ill_typed) do
    # soundness probe independent of the refinement gap: wrong-typed branch body.
    motive = {:lam, @dec, {:lam, {:data, :Ix, [], [{:var, 0}]}, @dec}}
    body = {:case, {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}, motive, [{:wrap, 1, {:type, 0}}]}
    challenge(:ill_typed, [dec_family(), ix_family()], :refine, @dec, body,
      "ill-typed: wrap branch body {:type,0} where Dec is expected")
  end

  # -- 4.4 motive well-formedness ---------------------------------------------
  @doc """
  Motive well-formedness obligation. `:ill_typed` over-applies the motive (an extra
  `:lam` layer beyond index_arity+1), so `apply_motive` leaves a residual `{:vlam,...}`
  which `infer_type_value_sort` rejects as {:error, :bad_motive}. (Do NOT under-apply
  — that crashes Eval.apply; see spec §4.4.)
  """
  @spec motive_wf(:well_typed | :ill_typed) :: Challenge.t()
  def motive_wf(:well_typed) do
    body = {:case, {:ctor, :Causal, []}, {:lam, @dec, @dec},
            [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}
    challenge(:well_typed, [dec_family()], :motive_wf, @dec, body, "well-formed motive λx:Dec. Dec")
  end

  def motive_wf(:ill_typed) do
    over = {:lam, @dec, {:lam, @dec, @dec}}   # one lam too many for a 0-index family
    body = {:case, {:ctor, :Causal, []}, over,
            [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}
    # def_type is irrelevant to the motive check; use @dec (check fails before it matters).
    challenge(:ill_typed, [dec_family()], :motive_wf, @dec, body, "over-applied motive → :bad_motive")
  end

  # -- 4.4b motive well-formedness: an INDEXED family as a Π DOMAIN -----------
  defp snat_family, do: {Inductive.family(:SNat, [], [{:d, @dec}], 0),
                         [Inductive.ctor(:snat0, [], [{:ctor, :Dcoupled, []}])]}

  @doc """
  Convoy-motive well-formedness: the motive body is a Π whose DOMAIN is an indexed
  family `SNat s` (the encoding of `with` sibling refinement). `check_motive_wf`
  used to reify the Π value and re-infer it, but `Quote.reify` collapses
  `{:vdata,name,args}` → `{:data,name,args,[]}` (it has no inductive signature to
  recover the param/index split), so an indexed-family domain re-inferred with
  `:arg_arity` and the motive was wrongly `:bad_motive` — a false negative.

    * `:well_typed` — `λs. Π(SNat s). Dec`. Now accepted (value-recursion classifies
      the `{:vdata,…}` domain by its family's declared level, no lossy round-trip).
    * `:ill_typed` — NEGATIVE CONTROL: `λs. Π(Dcoupled). Dec`, whose Π domain is a
      Dec VALUE (a constructor), NOT a type. The value-recursion must still reject
      it (`:bad_motive`); this proves the fix removes false negatives WITHOUT
      introducing false positives (accepting a non-type domain).
  """
  @spec motive_indexed_domain(:well_typed | :ill_typed) :: Challenge.t()
  def motive_indexed_domain(:well_typed) do
    motive = {:lam, @dec, {:pi, @snat_s, @dec}}
    def_type = {:pi, @dec, {:pi, @snat_s, @dec}}

    body =
      {:lam, @dec,
       {:case, {:var, 0}, motive,
        [
          {:Dcoupled, 0,
           {:lam, {:data, :SNat, [], [{:ctor, :Dcoupled, []}]}, {:ctor, :Dcoupled, []}}},
          {:Causal, 0,
           {:lam, {:data, :SNat, [], [{:ctor, :Causal, []}]}, {:ctor, :Dcoupled, []}}}
        ]}}

    challenge(:well_typed, [dec_family(), snat_family()], :motive_dom, def_type, body,
      "convoy motive λs. Π(SNat s). Dec — indexed family as Π domain (was false :bad_motive)")
  end

  def motive_indexed_domain(:ill_typed) do
    neg_motive = {:lam, @dec, {:pi, {:ctor, :Dcoupled, []}, @dec}}

    body =
      {:lam, @dec,
       {:case, {:var, 0}, neg_motive,
        [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]}}

    challenge(:ill_typed, [dec_family(), snat_family()], :motive_dom, @dec, body,
      "negative control: Π domain is a Dec value (Dcoupled), not a type → :bad_motive")
  end

  # -- 4.5 impossible-branch discharge (no-confusion) -------------------------
  @doc """
  Impossible-branch discharge obligation. `wrap` builds `Ix Causal`; on an
  `Ix Dcoupled` scrutinee the branch is unreachable and its deliberately
  ill-typed body (`{:type,0}` where `Dec` is expected) must NOT be checked
  (`:well_typed`, discharged). The `:ill_typed` variant makes the SAME branch
  REACHABLE (scrutinee `Ix Causal`), so its body must be checked and rejected —
  the antibody that goes red if discharge ever over-fires on a live branch.
  """
  @spec discharge(:well_typed | :ill_typed) :: Challenge.t()
  def discharge(:well_typed) do
    ix_dcoupled = {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}
    motive = {:lam, @dec, {:lam, {:data, :Ix, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, ix_dcoupled, @dec}
    body = {:lam, ix_dcoupled, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}
    challenge(:well_typed, [dec_family(), ix_family()], :discharge, def_type, body,
      "impossible wrap branch (scrutinee Ix Dcoupled) discharged, body not checked")
  end

  def discharge(:ill_typed) do
    ix_causal = {:data, :Ix, [], [{:ctor, :Causal, []}]}
    motive = {:lam, @dec, {:lam, {:data, :Ix, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, ix_causal, @dec}
    body = {:lam, ix_causal, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}
    challenge(:ill_typed, [dec_family(), ix_family()], :discharge, def_type, body,
      "ill-typed: wrap branch REACHABLE (scrutinee Ix Causal), {:type,0} body must be rejected")
  end

  # -- 4.6 constructor injectivity (spine descent) ----------------------------
  # Wr = MkWr(Dec): a unary wrapper, so an index can be constructor-headed WITH an
  # argument. IW(w:Wr) with iw:(p:Dec)->IW(MkWr Causal): the result index
  # MkWr(Causal) unifies with a scrutinee index MkWr(n) ONLY by descending through
  # the shared MkWr head (injectivity → unify_spine) to solve n := Causal. Without
  # injectivity the pair is :undecided and the equation is dropped.
  defp wr_family, do: {Inductive.family(:Wr, [], [], 0), [Inductive.ctor(:MkWr, [{:d, @dec}], [])]}

  defp iw_family,
    do: {Inductive.family(:IW, [], [{:w, @wr}], 0),
         [Inductive.ctor(:iw, [{:p, @dec}], [{:ctor, :MkWr, [{:ctor, :Causal, []}]}])]}

  # IW indexed by MkWr(var k).
  defp iw_mk(k), do: {:data, :IW, [], [{:ctor, :MkWr, [{:var, k}]}]}

  @doc """
  Constructor-injectivity obligation. `:well_typed` reuses an outer hypothesis
  `h : IW(MkWr n)` as `IW(MkWr Causal)` inside the `iw` branch — sound only
  because injectivity descends through `MkWr` to solve `n := Causal`. `:ill_typed`
  demands `IW(MkWr Dcoupled)` in the branch, an equation the match never
  entails (injectivity yields only `n := Causal`), so it must be rejected.
  """
  @spec injectivity(:well_typed | :ill_typed) :: Challenge.t()
  def injectivity(:well_typed) do
    def_type = {:pi, @dec, {:pi, iw_mk(0), {:pi, iw_mk(1), iw_mk(2)}}}
    motive = {:lam, @wr, {:lam, {:data, :IW, [], [{:var, 0}]}, {:data, :IW, [], [{:var, 1}]}}}
    body = {:lam, @dec, {:lam, iw_mk(0), {:lam, iw_mk(1), {:case, {:var, 0}, motive, [{:iw, 1, {:var, 2}}]}}}}
    challenge(:well_typed, [dec_family(), wr_family(), iw_family()], :inject, def_type, body,
      "n := Causal solved by descending through MkWr (injectivity); reuse h:IW(MkWr n) as IW(MkWr Causal)")
  end

  def injectivity(:ill_typed) do
    iw_dcoupled = {:data, :IW, [], [{:ctor, :MkWr, [{:ctor, :Dcoupled, []}]}]}
    def_type = {:pi, @dec, {:pi, iw_mk(0), {:pi, iw_mk(1), iw_dcoupled}}}
    motive = {:lam, @wr, {:lam, {:data, :IW, [], [{:var, 0}]}, iw_dcoupled}}
    body = {:lam, @dec, {:lam, iw_mk(0), {:lam, iw_mk(1), {:case, {:var, 0}, motive, [{:iw, 1, {:var, 2}}]}}}}
    challenge(:ill_typed, [dec_family(), wr_family(), iw_family()], :inject, def_type, body,
      "ill-typed: injectivity yields only n:=Causal; body needs IW(MkWr Dcoupled) — must be rejected")
  end

  # -- W3: deletion rule (pre-port banking spec §4 W3) -------------------------
  # IxN is indexed by a raw integer; wrapn's GROUND result index is the literal 3.
  # A scrutinee at `IxN 3` yields the index equation `3 ~ 3`, which no other
  # unifier clause consumes (not a var, not ctor/data-headed) — it is discharged
  # by the DELETION rule (r == s ⇒ consistent, kernel.ex `unify_one`). The branch
  # is therefore REACHABLE with no refinement.
  defp ixn_family,
    do:
      {Inductive.family(:IxN, [], [{:i, {:int_type}}], 0),
       [Inductive.ctor(:wrapn, [{:p, @dec}], [{:int_lit, 3}])]}

  @doc """
  Deletion-rule obligation. `:well_typed`: the reachable-via-deletion branch has a
  well-typed body and must be ACCEPTED — the antibody against deletion degrading
  to `:impossible` (which would discharge a live branch and, on the ill side,
  wrongly accept). `:ill_typed`: the same reachable branch with an ill-typed body
  (`{:type,0}` where `Dec` is expected) must be REJECTED — deletion must never
  skip the body check.
  """
  @spec deletion(:well_typed | :ill_typed) :: Challenge.t()
  def deletion(label) do
    ixn3 = {:data, :IxN, [], [{:int_lit, 3}]}
    motive = {:lam, {:int_type}, {:lam, {:data, :IxN, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, ixn3, @dec}

    branch_body =
      case label do
        :well_typed -> {:ctor, :Dcoupled, []}
        :ill_typed -> {:type, 0}
      end

    body = {:lam, ixn3, {:case, {:var, 0}, motive, [{:wrapn, 1, branch_body}]}}

    challenge(label, [dec_family(), ixn_family()], :delete, def_type, body,
      "deletion rule: index equation 3 ~ 3 is consistent (r==s); branch reachable, body #{label}")
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
