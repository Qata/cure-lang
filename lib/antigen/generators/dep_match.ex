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
      {2, closed_index({:ctor, :S, [@z]})}
    ])
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
