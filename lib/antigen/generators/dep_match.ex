defmodule Antigen.Generators.DepMatch do
  @moduledoc """
  Structure-directed generator for **dependent pattern matching** — well-typed
  `case` over the indexed family `Vec`, with an index-refining branch structure
  and (optionally) a dependent type-former motive. This is the reachability lever
  for the kernel's dependent-matching core, which no value-term generator reaches:
  `check_motive_wf` → `infer_type_value_sort` (dependent motive), `check_case_branches`,
  `unify_indices` (`bind_index` / `unify_one` / `unify_spine` / `rigid_index?`,
  including the `:impossible` unreachable-branch path), `specialize_branch_context`,
  `check_result_indices`, and `replace_branch_vars`.

  Three scrutinee shapes, all well-typed by construction over the v1 menu:

    * **variable index** `xs : Vec n` (ctx `[Vec n, Nat]`) — both branches
      reachable; `unify_indices` refines `n := Z` / `n := S k`.
    * **closed `Vec Z`** — the `vcons` branch is `:impossible` (unify `S k` ~ `Z`).
    * **closed `Vec (S Z)`** — the `vnil` branch is `:impossible` (unify `Z` ~ `S Z`).

  Motives: constant (`λm.λv. Nat|Bd`) or dependent (`λm.λv. Vec m`, whose body is
  a type-former over the bound index — the `infer_type_value_sort` driver). Branch
  bodies inhabit the motive at the refined index. The claimed `type` is exactly
  what `infer` returns (verified in the soundness test).
  """
  alias Antigen.{Gen, Challenge}

  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  @z {:ctor, :Z, []}
  @assays ["term/infer_check", "term/subject_reduction", "term/normalization"]

  # Ty's constructor index terms + matching branches (declaration order). Defined
  # at module top so every generator below reads them (module attributes resolve at
  # the textual point of use, so a later assignment would read nil).
  @ty_indices [
    @nat,
    @bd,
    {:int_type},
    {:float_type},
    {:pi, @nat, @nat},
    {:sigma, @nat, @nat},
    {:data, :Vec, [@z], []}
  ]
  @ty_branches [
    {:tnat, 0, @z},
    {:tbd, 0, @z},
    {:tint, 0, @z},
    {:tflt, 0, @z},
    {:tpi, 0, @z},
    {:tsig, 0, @z},
    {:tvec, 0, @z}
  ]

  defp vec(i), do: {:data, :Vec, [], [i]}

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@assays), fn assay ->
      Gen.bind(case_challenge(), fn {ctx, term, type} ->
        Gen.return(
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: ctx, type: type, term: term},
            note: "dependent match (indexed Vec case)"
          )
        )
      end)
    end)
  end

  defp case_challenge do
    Gen.frequency([
      # variable index, both branches reachable — constant-motive flavours whose
      # result type drives a distinct infer_type_value_sort clause via check_motive_wf
      {3, var_const(@nat, numeral())},
      {2, var_const(@bd, bd_lit())},
      {2, var_const({:type, 0}, small_type())},
      {2, var_const({:int_type}, int_lit())},
      {2, var_const({:float_type}, float_lit())},
      # dependent motives: Vec m (type-former) and Eq Nat m m (propositional)
      {3, var_index(:vec)},
      {2, var_index(:eq)},
      # closed indices — force an :impossible branch (constant Nat motive)
      {2, closed_index(@z)},
      {2, closed_index({:ctor, :S, [@z]})},
      # extra context variable whose TYPE mentions the scrutinee index — branch
      # refinement specializes it via specialize_branch_context, driving
      # replace_branch_vars over Eq / Σ / Π type shapes.
      {2, var_index_extra({:eq, @nat, {:var, 1}, {:var, 1}})},
      {2, var_index_extra({:sigma, @nat, vec({:var, 2})})},
      {2, var_index_extra({:pi, @nat, vec({:var, 2})})},
      # extra context types carrying stuck value-level subterms (λ / pair / refl)
      # so specialize_branch_context's replace_branch_vars descends those arms.
      {2, var_index_extra({:eq, {:pi, @nat, @nat}, {:lam, @nat, {:var, 0}}, {:lam, @nat, {:var, 0}}})},
      {2, var_index_extra({:eq, {:sigma, @nat, @nat}, {:pair, {:var, 1}, {:var, 1}}, {:pair, {:var, 1}, {:var, 1}}})},
      {2, var_index_extra({:eq, {:eq, @nat, {:var, 1}, {:var, 1}}, {:refl, {:var, 1}}, {:refl, {:var, 1}}})},
      # two-var frame: a helper context var lets extra_ty carry a STUCK app /
      # projection / prim — replace_branch_vars' app/fst/snd/prim arms.
      {2, var_index_extra2({:pi, @nat, @nat}, {:eq, @nat, {:app, {:var, 1}, {:var, 3}}, {:app, {:var, 1}, {:var, 3}}})},
      {2, var_index_extra2({:sigma, @nat, @nat}, {:eq, @nat, {:fst, {:var, 1}}, {:fst, {:var, 1}}})},
      {2, var_index_extra2({:sigma, @nat, @nat}, {:eq, @nat, {:snd, {:var, 1}}, {:snd, {:var, 1}}})},
      {2, var_index_extra2({:int_type}, {:eq, {:int_type}, {:prim, :add, [{:var, 1}, {:var, 1}]}, {:prim, :add, [{:var, 1}, {:var, 1}]}})},
      # TWO-index diagonal family Sq — matching forces a ≡ b, the only v1 shape
      # that reaches unify_spine (2-index spine) + bind_index's merge path.
      {3, sq_diag()},
      {2, sq_closed(@z, @z)},
      {2, sq_closed(@z, {:ctor, :S, [@z]})},
      # Type0-indexed family Ty — a closed type index unified against each ctor's
      # rigid type index (rigid_index? data/int/float/Π/Σ, head_key :data,
      # unify_one data-spine / syntactic-equal). Random concrete index + a var index.
      {4, ty_closed()},
      {2, ty_var()},
      # Ty with a Vec (S Z) index that matches NO ctor — unifying against tvec's
      # Vec Z index drives unify_spine to :impossible on a differing element.
      {1, ty_scrutinee({:data, :Vec, [{:ctor, :S, [@z]}], []})},
      # Int/Float-value-indexed families Tg/Tgf — literal indices unified at match
      # time (rigid_index? int_lit/float_lit).
      {2, tg_closed(:int)},
      {2, tg_closed(:float)}
    ])
  end

  # Closed scrutinee x : Ty T for an ARBITRARY closed type index (possibly matching
  # no ctor — all branches then unify T against a differing rigid index).
  defp ty_scrutinee(idx) do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, ty_motive(), replace_first_body(@ty_branches, body))
      Gen.return({[ty(idx)], term, @nat})
    end)
  end

  @tg %{
    int: {:Tg, [{:tg0, 0, @z}, {:tg1, 0, @z}], [{:int_lit, 0}, {:int_lit, 1}, {:int_lit, 5}]},
    float: {:Tgf, [{:tgf0, 0, @z}, {:tgf1, 0, @z}], [{:float_lit, 0.0}, {:float_lit, 1.5}, {:float_lit, 2.5}]}
  }

  # Closed scrutinee x : Tg <lit> (Int/Float-indexed) — matching unifies the closed
  # literal index against each ctor's literal result index.
  defp tg_closed(kind) do
    {fname, branches, indices} = @tg[kind]

    Gen.bind(Gen.member_of(indices), fn idx ->
      Gen.bind(numeral(), fn body ->
        brs = replace_first_body(branches, body)
        term = mk_case({:var, 0}, tg_motive(fname, kind), brs)
        Gen.return({[{:data, fname, [], [idx]}], term, @nat})
      end)
    end)
  end

  defp tg_motive(fname, kind) do
    ity = if kind == :int, do: {:int_type}, else: {:float_type}
    {:lam, ity, {:lam, {:data, fname, [], [{:var, 0}]}, @nat}}
  end

  # Closed scrutinee x : Ty T for a random concrete type index T. The matching ctor
  # is trivial/solved; the rest unify T against a differing rigid head (:impossible
  # or :undecided) — the rigid_index?/head_key comparison lever.
  defp ty_closed do
    Gen.bind(Gen.member_of(@ty_indices), fn idx ->
      Gen.bind(numeral(), fn body ->
        term = mk_case({:var, 0}, ty_motive(), replace_first_body(@ty_branches, body))
        Gen.return({[ty(idx)], term, @nat})
      end)
    end)
  end

  # Variable index x : Ty a (a : Type0) — every ctor's rigid type index is bound to a.
  defp ty_var do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, ty_motive(), replace_first_body(@ty_branches, body))
      Gen.return({[ty({:var, 0}), {:type, 0}], term, @nat})
    end)
  end

  defp ty(a), do: {:data, :Ty, [], [a]}
  # λa. λv:Ty a. Nat
  defp ty_motive, do: {:lam, {:type, 0}, {:lam, ty({:var, 0}), @nat}}
  # vary the reachable-branch body without disturbing the fixed ctor set
  defp replace_first_body([{c, ar, _} | rest], body), do: [{c, ar, body} | rest]

  # Γ = [ s : Sq a b (idx 0), b : Nat (idx 1), a : Nat (idx 2) ]; matching mksq
  # unifies the diagonal result index against both a and b → forces a ≡ b.
  defp sq_diag do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, sq_motive(), [{:mksq, 1, body}])
      Gen.return({[sq({:var, 1}, {:var, 0}), @nat, @nat], term, @nat})
    end)
  end

  # Closed Sq indices: Sq Z Z (mksq trivial) / Sq Z (S Z) (mksq :impossible).
  defp sq_closed(i, j) do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, sq_motive(), [{:mksq, 1, body}])
      Gen.return({[sq(i, j)], term, @nat})
    end)
  end

  defp sq(i, j), do: {:data, :Sq, [], [i, j]}
  # λi.λj.λv:Sq i j. Nat  (v's frame: i = var 2, j = var 1)
  defp sq_motive, do: {:lam, @nat, {:lam, @nat, {:lam, sq({:var, 2}, {:var, 1}), @nat}}}

  # Γ = [ p : extra_ty (idx 0), xs : Vec n (idx 1), n : Nat (idx 2) ] where
  # extra_ty mentions n (var 1 from p's frame). Scrutinee is xs (var 1). When a
  # branch refines n, `specialize_branch_context` rewrites p's type — exercising
  # `replace_branch_vars` over extra_ty's shape.
  defp var_index_extra(extra_ty) do
    Gen.bind(numeral(), fn zbody ->
      Gen.bind(numeral(), fn sbody ->
        term = mk_case({:var, 1}, motive(@nat), [{:vnil, 0, zbody}, {:vcons, 3, sbody}])
        Gen.return({[extra_ty, vec({:var, 0}), @nat], term, @nat})
      end)
    end)
  end

  # Like var_index_extra but with an extra HELPER context var (a function / Σ /
  # Int) so `extra_ty` can carry a value-level subterm that stays STUCK through
  # evaluation — `helper n` (app), `fst/snd helper` (projections), `prim add
  # [helper,helper]` — driving replace_branch_vars' app/fst/snd/prim arms when a
  # branch refines the index. Frame: Γ = [extra_ty, helper_ty, Vec n, n:Nat]; the
  # scrutinee is var 2, the helper var 1, and `n` var 3 inside extra_ty.
  defp var_index_extra2(helper_ty, extra_ty) do
    Gen.bind(numeral(), fn zbody ->
      Gen.bind(numeral(), fn sbody ->
        term = mk_case({:var, 2}, motive(@nat), [{:vnil, 0, zbody}, {:vcons, 3, sbody}])
        Gen.return({[extra_ty, helper_ty, vec({:var, 0}), @nat], term, @nat})
      end)
    end)
  end

  # Γ = [ xs : Vec n (idx 0), n : Nat (idx 1) ]; case xs of vnil | vcons, with a
  # CONSTANT motive λm.λv. result_ty — both branch bodies inhabit result_ty. The
  # motive body's shape (universe / Int / Float / data) selects the
  # infer_type_value_sort clause exercised.
  defp var_const(result_ty, body_gen) do
    Gen.bind(body_gen, fn zbody ->
      Gen.bind(body_gen, fn sbody ->
        term = mk_case({:var, 0}, motive(result_ty), [{:vnil, 0, zbody}, {:vcons, 3, sbody}])
        Gen.return({[vec({:var, 0}), @nat], term, result_ty})
      end)
    end)
  end

  # Dependent motive λm.λv. Eq Nat m m — branch bodies are refl at the refined
  # index (vnil : Eq Nat Z Z → refl Z; vcons : Eq Nat (S n) (S n) → refl (S n)).
  defp var_index(:eq) do
    eq_ty = fn m -> {:eq, @nat, m, m} end
    motive_eq = {:lam, @nat, {:lam, vec({:var, 0}), eq_ty.({:var, 1})}}
    nil_body = {:refl, @z}
    cons_body = {:refl, {:ctor, :S, [{:var, 2}]}}
    term = mk_case({:var, 0}, motive_eq, [{:vnil, 0, nil_body}, {:vcons, 3, cons_body}])
    Gen.return({[vec({:var, 0}), @nat], term, eq_ty.({:var, 1})})
  end

  # Dependent motive λm.λv. Vec m — branch bodies must inhabit Vec at the refined
  # index (vnil : Vec Z; vcons n x xs : Vec (S n)).
  defp var_index(:vec) do
    nil_body = {:ctor, :vnil, []}
    cons_body = {:ctor, :vcons, [{:var, 2}, {:var, 1}, {:var, 0}]}
    term = mk_case({:var, 0}, dep_motive(), [{:vnil, 0, nil_body}, {:vcons, 3, cons_body}])
    # infer normalizes Vec's sole argument into the PARAMS slot (empty indices) —
    # the claimed type must match that reified normal form (see Generators.Term).
    Gen.return({[vec({:var, 0}), @nat], term, {:data, :Vec, [{:var, 1}], []}})
  end

  # Γ = [ xs : Vec <idx> (idx 0) ] with a closed index → one branch is :impossible.
  # Constant Nat motive; the reachable branch's body is a numeral, the impossible
  # branch's body is unchecked (any well-formed term).
  defp closed_index(idx) do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, motive(@nat), [{:vnil, 0, body}, {:vcons, 3, @z}])
      Gen.return({[vec(idx)], term, @nat})
    end)
  end

  # motive λm. λv:Vec m. <ty>  (constant result type)
  defp motive(ty), do: {:lam, @nat, {:lam, vec({:var, 0}), ty}}
  # dependent motive λm. λv:Vec m. Vec m
  defp dep_motive, do: {:lam, @nat, {:lam, vec({:var, 0}), vec({:var, 1})}}

  defp mk_case(scrut, motive, branches), do: {:case, scrut, motive, branches}

  defp numeral do
    Gen.bind(Gen.int(0, 4), fn n ->
      Gen.return(Enum.reduce(1..n//1, @z, fn _, acc -> {:ctor, :S, [acc]} end))
    end)
  end

  defp bd_lit, do: Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}])

  # A closed type inhabiting Type 0 (for a λm.λv.Type0 motive's branch bodies).
  defp small_type, do: Gen.member_of([@nat, @bd, {:int_type}, {:float_type}])
  defp int_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end)
  defp float_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
end
