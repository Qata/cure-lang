defmodule Cure.Elab.Elaborator do
  @moduledoc """
  Elaborate the surface expression fragment into explicit `Cure.Core` terms
  (design spec §5; mirrors Idris `TTImp/Elab/Check.idr`).

  Untrusted: it resolves names to de Bruijn indices and builds Core terms that
  the kernel then re-checks. This task covers the basic fragment — `Type`,
  function definitions (→ λ / Π), variables, and application. Implicit inference
  (M8.2), erasure marking (M8.3), and dependent pattern compilation (M8.4) build
  on it.

  A *scope* is the list of in-scope binder names, most-recently-bound first, so a
  name resolves to its de Bruijn index by position.
  """

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel, Quote}
  alias Cure.Elab.{MetaCtx, Subst, Unify}

  @doc """
  Elaborate a top-level function definition into `{:ok, core_lambda, type_value}`
  — the λ over the parameters and the Π type it inhabits.
  """
  @spec elaborate(tuple(), Env.t()) :: {:ok, Cure.Core.Term.t(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate({:function_def, meta, body}, env) do
    params = Keyword.get(meta, :params, [])
    return_expr = Keyword.fetch!(meta, :return_type)

    with {:ok, param_tele} <- elaborate_params(params, [], env),
         scope = param_tele |> Enum.map(&elem(&1, 0)) |> Enum.reverse(),
         {:ok, body_core} <- elaborate_expr(single_body(body), scope, env),
         {:ok, return_core} <- elaborate_type(return_expr, scope, env) do
      lambda = wrap(:lam, param_tele, body_core)
      pi = wrap(:pi, param_tele, return_core)
      {:ok, lambda, Eval.eval(pi, [])}
    end
  end

  def elaborate(other, _env), do: {:error, {:unsupported_expression, other}}

  @doc """
  Context-aware expression elaboration: elaborate `expr` to `{term, type_value}`
  in a kernel typing `ctx` (whose variables are named, most-recently-bound first,
  by `names`). Constructor applications route through `elaborate_ctor_app/3` so
  their erased indices are inferred; other forms reuse the untyped elaborator and
  the kernel's `infer/2` for their type.
  """
  @spec elaborate_expr_typed(term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate_expr_typed({:variable, _meta, "Type"}, _names, _ctx, _env),
    do: {:ok, {:type, 0}, {:vtype, 1}}

  def elaborate_expr_typed({:variable, _meta, name}, names, ctx, env) do
    case Enum.find_index(names, &(&1 == name)) do
      nil ->
        with {:ok, term} <- resolve_free(name, env),
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end

      index ->
        term = {:var, index}

        with {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end
    end
  end

  def elaborate_expr_typed({:function_call, meta, args}, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    cond do
      name == "refl" and length(args) == 1 ->
        [arg] = args

        with {:ok, arg_term, _type} <- elaborate_expr_typed(arg, names, ctx, env),
             term = {:refl, arg_term},
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end

      Inductive.get_ctor(env, atom) ->
        with {:ok, present} <- map_present_args(args, names, ctx, env) do
          elaborate_ctor_app(env, atom, present)
        end

      # A global whose telescope carries erased (implicit) parameters: insert
      # fresh metavariables for them and solve from the present arguments, the
      # same way constructor indices are inferred (§5.2). Without this, the
      # explicit args would be bound to the implicit positions.
      implicit_def?(env, atom) ->
        with {:ok, present} <- map_present_args(args, names, ctx, env) do
          elaborate_global_app(env, atom, present, ctx)
        end

      true ->
        # Non-constructor application: elaborate to a term, then let the kernel type it.
        with {:ok, term} <- elaborate_expr({:function_call, [name: name], args}, names, env),
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end
    end
  end

  def elaborate_expr_typed({:attribute_access, meta, [inner]}, names, ctx, env) do
    with {:ok, inner_term, _type} <- elaborate_expr_typed(inner, names, ctx, env) do
      term =
        case Keyword.fetch!(meta, :attribute) do
          "1" -> {:fst, inner_term}
          "2" -> {:snd, inner_term}
        end

      with {:ok, type} <- Kernel.infer(ctx, term), do: {:ok, term, type}
    end
  end

  def elaborate_expr_typed({:rewrite_expr, _meta, _children}, _names, _ctx, _env),
    do: {:error, :rewrite_requires_expected_type}

  def elaborate_expr_typed(other, _names, _ctx, _env), do: {:error, {:unsupported_expression, other}}

  @doc """
  Checking-mode elaboration for proof forms whose Core term depends on the
  expected type. Ordinary expressions fall back to infer-then-check.
  """
  @spec elaborate_expr_checked(term(), term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term()} | {:error, term()}
  def elaborate_expr_checked({:function_call, meta, [arg]} = expr, expected_core, names, ctx, env) do
    if Keyword.get(meta, :name) == "refl" do
      with {:ok, arg_term, _type} <- elaborate_expr_typed(arg, names, ctx, env),
           term = {:refl, arg_term},
           :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
        {:ok, term}
      end
    else
      elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
    end
  end

  def elaborate_expr_checked({:rewrite_expr, _meta, [proof_ast, body_ast]}, expected_core, names, ctx, env) do
    depth = Context.length(ctx)

    with {:ok, proof_term, proof_type} <- elaborate_expr_typed(proof_ast, names, ctx, env),
         {:ok, ty_value, a_value, b_value} <- eq_parts(proof_type),
         ty = Kernel.normalize(ctx, Quote.reify(ty_value, depth)),
         a = Kernel.normalize(ctx, Quote.reify(a_value, depth)),
         b = Kernel.normalize(ctx, Quote.reify(b_value, depth)),
         normalized_expected = Kernel.normalize(ctx, expected_core),
         {:ok, proof, motive, body_expected} <- rewrite_plan(proof_term, ty, a, b, normalized_expected),
         {:ok, body_term} <- elaborate_expr_checked(body_ast, body_expected, names, ctx, env),
         term = {:rewrite, proof, motive, body_term},
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  def elaborate_expr_checked(expr, expected_core, names, ctx, env),
    do: elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

  defp elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env) do
    with {:ok, term, _type} <- elaborate_expr_typed(expr, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  defp eq_parts({:veq, ty, a, b}), do: {:ok, ty, a, b}
  defp eq_parts(_other), do: {:error, :rewrite_proof_not_equality}

  # Core rewrite transports M[a] -> M[b]. Idris-style source `rewrite p in t`
  # checks `t` under the rewritten goal and returns the original goal, so when
  # the expected type contains the proof's left endpoint we synthesize symmetry.
  defp rewrite_plan(proof, ty, a, b, expected) do
    cond do
      contains_term?(expected, a) ->
        with {:ok, sym_proof} <- symmetry_proof(proof, ty, a, b),
             {:ok, motive} <- motive_for(expected, a, ty) do
          {:ok, sym_proof, motive, replace_term(expected, a, b)}
        end

      contains_term?(expected, b) ->
        {:ok, motive} = motive_for(expected, b, ty)
        {:ok, proof, motive, replace_term(expected, b, a)}

      true ->
        {:error, {:rewrite_no_match, a, b, expected}}
    end
  end

  defp symmetry_proof(proof, ty, a, _b) do
    motive_body = {:eq, Subst.shift(ty, 1, 0), {:var, 0}, Subst.shift(a, 1, 0)}
    motive = {:lam, ty, motive_body}
    {:ok, {:rewrite, proof, motive, {:refl, a}}}
  end

  defp motive_for(expected, target, ty), do: {:ok, {:lam, ty, abstract_term(expected, target, 0)}}

  defp contains_term?(term, target), do: term == target or Enum.any?(children(term), &contains_term?(&1, target))

  defp replace_term(term, target, replacement) when term == target, do: replacement

  defp replace_term(term, target, replacement) when is_list(term),
    do: Enum.map(term, &replace_term(&1, target, replacement))

  defp replace_term(term, target, replacement) do
    if term == target do
      replacement
    else
      rebuild(term, Enum.map(children(term), &replace_term(&1, target, replacement)))
    end
  end

  defp abstract_term(term, target, depth) when term == target, do: {:var, depth}
  defp abstract_term({:var, i}, _target, depth) when i >= depth, do: {:var, i + 1}
  defp abstract_term({:var, _} = var, _target, _depth), do: var

  defp abstract_term({:pi, d, c}, target, depth),
    do: {:pi, abstract_term(d, target, depth), abstract_term(c, target, depth + 1)}

  defp abstract_term({:lam, d, b}, target, depth),
    do: {:lam, abstract_term(d, target, depth), abstract_term(b, target, depth + 1)}

  defp abstract_term({:sigma, a, b}, target, depth),
    do: {:sigma, abstract_term(a, target, depth), abstract_term(b, target, depth + 1)}

  # A `:case` branch `{ctor, arity, body}` binds `arity` de Bruijn variables in
  # `body` (see `Cure.Core.Term` shift/3's `:case` clause). Mirror that here:
  # abstract the scrutinee and motive at `depth`, but each branch body at
  # `depth + arity`, so branch-bound variables in `[depth, depth+arity)` are not
  # spuriously shifted by the `{:var, i} when i >= depth` clause. Without this,
  # the generic tuple clause below recurses into branch bodies at the wrong
  # depth and corrupts the motive (P0 Task 5, rewrite goals with a stuck `case`).
  defp abstract_term({:case, scrut, motive, branches}, target, depth) do
    {:case, abstract_term(scrut, target, depth), abstract_term(motive, target, depth),
     Enum.map(branches, fn {ctor, arity, body} ->
       {ctor, arity, abstract_term(body, target, depth + arity)}
     end)}
  end

  defp abstract_term(term, target, depth) when is_tuple(term),
    do: rebuild(term, Enum.map(children(term), &abstract_term(&1, target, depth)))

  defp abstract_term(term, target, depth) when is_list(term),
    do: Enum.map(term, &abstract_term(&1, target, depth))

  defp abstract_term(term, _target, _depth), do: term

  defp children(term) when is_tuple(term), do: term |> Tuple.to_list() |> tl()
  defp children(term) when is_list(term), do: term
  defp children(_term), do: []

  defp rebuild(term, children) when is_tuple(term) do
    [elem(term, 0) | children] |> List.to_tuple()
  end

  defp rebuild(term, _children), do: term

  defp implicit_def?(env, atom) do
    case Env.get_def(env, atom) do
      %{quantities: q} when is_list(q) -> :erased in q
      _ -> false
    end
  end

  defp map_present_args(args, names, ctx, env) do
    depth = Context.length(ctx)

    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case elaborate_expr_typed(arg, names, ctx, env) do
        # Reify the argument's type at the *context* depth so its de Bruijn
        # indices are in the caller's frame (where the erased indices are solved).
        {:ok, term, type} -> {:cont, {:ok, acc ++ [{term, Quote.reify(type, depth)}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  @doc """
  Elaborate a surface `match scrut | C(pat…) -> body …` into a Core `:case`
  (design spec §5, M8.4). `result_type_term` is the expected result type (Core
  term in the current frame); the motive is built as a constant type family over
  the scrutinee family's indices and value (dependent motives — a result that
  varies with the matched indices — are a follow-up). Branch bodies are
  elaborated under the constructor's full telescope (erased indices + present
  args); surface pattern variables name the present positions. Coverage and
  per-branch index refinement are then enforced by the kernel.
  """
  @spec elaborate_match(term(), [tuple()], term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term()} | {:error, term()}
  def elaborate_match(scrut_expr, arms, result_type_term, names, ctx, env) do
    with {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)
          # The scrutinee's args are parameters ++ indices; split off the leading
          # parameters. Only the indices are abstracted by the motive and refined
          # per branch — parameters are uniform (never matched).
          pc = Inductive.param_count(env, dname)
          {param_vals, idx_vals} = Enum.split(combined_vals, pc)
          param_terms = Enum.map(param_vals, &Quote.reify(&1, Context.length(ctx)))
          idx_terms = Enum.map(idx_vals, &Quote.reify(&1, Context.length(ctx)))

          motive =
            build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)

          with {:ok, branches} <-
                 elaborate_branches(
                   arms, names, ctx, env, dname,
                   idx_vals, idx_terms, param_vals, scrut_term, result_type_term
                 ) do
            {:ok, {:case, scrut_term, motive, branches}}
          end

        _ ->
          {:error, :match_scrutinee_not_data}
      end
    end
  end

  # motive = λ(j₀:T₀)…λ(jₙ:Tₙ).λ(x : D j̄). ResultType[scrutinee-indices ↦ j̄]
  #
  # The result type is *generalized* over the scrutinee's index arguments: where
  # the scrutinee is `x : D ā` with each aₖ a variable, every occurrence of aₖ in
  # ResultType is rebound to the motive's k-th index binder. Each branch is then
  # checked with that index specialized to the constructor's computed index —
  # this is what refines `m` to `Z`/`S k` in `match (xs : Vec a m)` so a result
  # like `Vec a (plus m n)` typechecks per branch. When ResultType doesn't
  # mention an index variable the generalization is a no-op, degrading to the
  # constant motive.
  defp build_motive(dname, index_tele, param_terms, idx_terms, scrut_term, result_type_term) do
    k = length(index_tele)
    index_types = Enum.map(index_tele, &elem(&1, 1))
    # The scrutinee-binder type `D params̄ j̄` sits under the k index binders j̄;
    # the parameters were reified in the outer frame, so shift them past the k
    # binders. Parameters are uniform, so they are constant across branches (no
    # generalization) — only the indices become the fresh binders `(k-1)..0`.
    param_terms_shifted = Enum.map(param_terms, &Subst.shift(&1, k, 0))
    scrut_type = {:data, dname, param_terms_shifted, Enum.map((k - 1)..0//-1, &{:var, &1})}

    # Map each scrutinee index *variable* (in the current frame) to the de Bruijn
    # index of its motive binder jₖ (which sits at depth k-pos above the body).
    rebind =
      idx_terms
      |> Enum.with_index()
      |> Enum.reduce(%{}, fn
        {{:var, orig}, pos}, acc -> Map.put(acc, orig, k - pos)
        {_non_var, _pos}, acc -> acc
      end)

    rebind =
      case scrut_term do
        {:var, orig} -> Map.put(rebind, orig, 0)
        _other -> rebind
      end

    body = generalize(result_type_term, rebind, k + 1, 0)

    (index_types ++ [scrut_type])
    |> Enum.reverse()
    |> Enum.reduce(body, fn type, acc -> {:lam, type, acc} end)
  end

  # Rewrite the free variables of `term` for placement under the motive's k+1
  # binders (`depth` counts binders entered *within* term): a free variable that
  # names a scrutinee index becomes its motive binder (`rebind`); every other
  # free variable is shifted past the new binders (`shift`).
  defp generalize({:var, i}, _rebind, _shift, depth) when i < depth, do: {:var, i}

  defp generalize({:var, i}, rebind, shift, depth) do
    orig = i - depth

    case Map.fetch(rebind, orig) do
      {:ok, binder} -> {:var, binder + depth}
      :error -> {:var, orig + shift + depth}
    end
  end

  defp generalize({:pi, d, c}, rb, s, depth),
    do: {:pi, generalize(d, rb, s, depth), generalize(c, rb, s, depth + 1)}

  defp generalize({:lam, d, b}, rb, s, depth),
    do: {:lam, generalize(d, rb, s, depth), generalize(b, rb, s, depth + 1)}

  defp generalize({:sigma, a, b}, rb, s, depth),
    do: {:sigma, generalize(a, rb, s, depth), generalize(b, rb, s, depth + 1)}

  defp generalize({:app, f, a}, rb, s, depth),
    do: {:app, generalize(f, rb, s, depth), generalize(a, rb, s, depth)}

  defp generalize({:pair, a, b}, rb, s, depth),
    do: {:pair, generalize(a, rb, s, depth), generalize(b, rb, s, depth)}

  defp generalize({:fst, p}, rb, s, depth), do: {:fst, generalize(p, rb, s, depth)}
  defp generalize({:snd, p}, rb, s, depth), do: {:snd, generalize(p, rb, s, depth)}

  defp generalize({:data, n, ps, is}, rb, s, depth),
    do: {:data, n, Enum.map(ps, &generalize(&1, rb, s, depth)), Enum.map(is, &generalize(&1, rb, s, depth))}

  defp generalize({:ctor, n, args}, rb, s, depth),
    do: {:ctor, n, Enum.map(args, &generalize(&1, rb, s, depth))}

  defp generalize({:case, scr, m, brs}, rb, s, depth),
    do:
      {:case, generalize(scr, rb, s, depth), generalize(m, rb, s, depth),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, generalize(b, rb, s, depth + ar)} end)}

  defp generalize({:eq, t, a, b}, rb, s, depth),
    do: {:eq, generalize(t, rb, s, depth), generalize(a, rb, s, depth), generalize(b, rb, s, depth)}

  defp generalize({:refl, a}, rb, s, depth), do: {:refl, generalize(a, rb, s, depth)}

  defp generalize({:rewrite, p, m, b}, rb, s, depth),
    do: {:rewrite, generalize(p, rb, s, depth), generalize(m, rb, s, depth), generalize(b, rb, s, depth)}

  defp generalize({:prim, op, args}, rb, s, depth),
    do: {:prim, op, Enum.map(args, &generalize(&1, rb, s, depth))}

  defp generalize(leaf, _rb, _s, _depth), do: leaf

  # Coverage/discharge pass (spec §5). Partition the surface arms, then emit a
  # branch for EVERY declared constructor of `dname` — matched arms elaborate
  # their bodies; omitted or explicit-impossible constructors are discharged
  # (verdict :impossible ⇒ {:absurd} placeholder body) or rejected. The kernel
  # then re-checks and re-discharges the assembled {:case,…} independently.
  # `idx_vals` are the scrutinee's index VALUES (for branch_unify); `idx_terms`
  # are the reified index TERMS (for branch_expected/context).
  defp elaborate_branches(arms, names, ctx, env, dname, idx_vals, idx_terms, param_vals, scrut_term, result_type_term) do
    with {:ok, arm_map} <- partition_arms(arms, ctx, env, dname) do
      sig = Context.signature(ctx)

      sig
      |> Inductive.ctors_of(dname)
      |> Enum.map(& &1.name)
      |> Enum.reduce_while({:ok, []}, fn cname, {:ok, acc} ->
        verdict = Kernel.branch_unify(ctx, dname, cname, idx_vals)

        case Map.get(arm_map, cname) do
          {:matched, pattern, body_expr} ->
            case elaborate_matched_branch(
                   verdict, pattern, body_expr, names, ctx, env,
                   idx_terms, param_vals, scrut_term, result_type_term
                 ) do
              {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
              {:error, _} = err -> {:halt, err}
            end

          {:impossible_marked, pattern} ->
            if verdict == :impossible do
              {arity, _} = ctor_arity(env, pattern)
              {:cont, {:ok, acc ++ [{cname, arity, {:absurd}}]}}
            else
              {:halt, {:error, {:reachable_impossible, cname}}}
            end

          nil ->
            # omitted constructor
            if verdict == :impossible do
              {arity, _} = ctor_arity(env, cname)
              {:cont, {:ok, acc ++ [{cname, arity, {:absurd}}]}}
            else
              {:halt, {:error, {:missing_branch, cname}}}
            end
        end
      end)
    end
  end

  # Build a map cname => {:matched, pattern, body} | {:impossible_marked, pattern}.
  # Validates every arm names one of dname's OWN declared constructors (spec §5
  # step 2 gap) and rejects duplicate arms.
  defp partition_arms(arms, ctx, env, dname) do
    sig = Context.signature(ctx)

    Enum.reduce_while(arms, {:ok, %{}}, fn {:match_arm, arm_meta, body}, {:ok, acc} ->
      pattern = Keyword.fetch!(arm_meta, :pattern)

      case constructor_pattern(pattern) do
        {:error, _} = err ->
          {:halt, err}

        {:ok, {cname, _vars}} ->
          cond do
            Inductive.get_ctor(env, cname) == nil ->
              {:halt, {:error, {:unknown_pattern_constructor, cname}}}

            Inductive.ctor_family(sig, cname) != dname ->
              {:halt, {:error, {:foreign_ctor, cname}}}

            Map.has_key?(acc, cname) ->
              {:halt, {:error, {:duplicate_branch, cname}}}

            Keyword.get(arm_meta, :impossible) == true ->
              {:cont, {:ok, Map.put(acc, cname, {:impossible_marked, pattern})}}

            true ->
              {:cont, {:ok, Map.put(acc, cname, {:matched, pattern, single_body(body)})}}
          end
      end
    end)
  end

  # Arity of a constructor named directly or by a pattern (spec §5 steps 4/5).
  defp ctor_arity(env, {:function_call, _, _} = pattern) do
    {:ok, {cname, _}} = constructor_pattern(pattern)
    ctor_arity(env, cname)
  end

  defp ctor_arity(env, cname) when is_atom(cname) do
    %{args: tele} = Inductive.get_ctor(env, cname)
    {length(tele), cname}
  end

  defp elaborate_matched_branch(verdict, pattern, body_expr, names, ctx, env, scrut_indices, scrut_param_vals, scrut_term, result_type_term) do
    {:ok, {cname, pattern_vars}} = constructor_pattern(pattern)
    %{args: telescope, quantities: quantities, result_indices: result_indices} = Inductive.get_ctor(env, cname)
    branch_names = branch_scope(quantities, pattern_vars) ++ names

    case verdict do
      :impossible ->
        # Matched arm on a genuinely unreachable constructor the user did NOT mark
        # impossible: elaborate the body unchecked (the kernel discharges it too).
        branch_ctx = extend_context(ctx, telescope, scrut_param_vals)

        with {:ok, body_term, _type} <- elaborate_expr_typed(body_expr, branch_names, branch_ctx, env) do
          {:ok, {cname, length(telescope), body_term}}
        end

      _solved_or_trivial ->
        branch_ctx =
          ctx
          |> extend_context(telescope, scrut_param_vals)
          |> specialize_branch_context(result_indices, scrut_indices, length(telescope))

        branch_expected =
          result_type_term
          |> branch_expected_type(scrut_term, cname, length(telescope), result_indices, scrut_indices)
          |> then(&Kernel.normalize(branch_ctx, &1))

        with {:ok, body_term} <- elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
          {:ok, {cname, length(telescope), body_term}}
        end
    end
  end

  defp elaborate_branch_body({:rewrite_expr, _meta, _children} = expr, expected, names, ctx, env),
    do: elaborate_expr_checked(expr, expected, names, ctx, env)

  defp elaborate_branch_body({:function_call, meta, _args} = expr, expected, names, ctx, env) do
    if Keyword.get(meta, :name) == "refl" do
      elaborate_expr_checked(expr, expected, names, ctx, env)
    else
      with {:ok, term, _type} <- elaborate_expr_typed(expr, names, ctx, env), do: {:ok, term}
    end
  end

  defp elaborate_branch_body(expr, _expected, names, ctx, env) do
    with {:ok, term, _type} <- elaborate_expr_typed(expr, names, ctx, env), do: {:ok, term}
  end

  defp constructor_pattern({:function_call, meta, args}) do
    cname = meta |> Keyword.fetch!(:name) |> String.to_atom()
    vars = Enum.map(args, fn {:variable, _meta, v} -> v end)
    {:ok, {cname, vars}}
  end

  defp constructor_pattern(other), do: {:error, {:unsupported_pattern, pattern_shape(other)}}

  defp pattern_shape(p) when is_tuple(p) and tuple_size(p) > 0, do: elem(p, 0)
  defp pattern_shape(_), do: :unknown

  # Names for the branch's telescope binders, most-recently-bound first: surface
  # pattern variables name the present (ω) positions in order; erased positions
  # are inaccessible, given a fresh placeholder.
  defp branch_scope(quantities, pattern_vars) do
    {names_in_order, _rest} =
      Enum.map_reduce(quantities, pattern_vars, fn
        :present, [v | rest] -> {v, rest}
        :erased, vars -> {"_erased", vars}
      end)

    Enum.reverse(names_in_order)
  end

  defp branch_expected_type(result_type_term, scrut_term, cname, arity, result_indices, scrut_indices) do
    shifted = Subst.shift(result_type_term, arity, 0)
    subst = branch_index_subst(result_indices, scrut_indices, arity)

    subst =
      case scrut_term do
        {:var, i} -> Map.put(subst, i + arity, branch_constructor_term(cname, arity))
        _other -> subst
      end

    replace_branch_vars(shifted, subst)
  end

  defp branch_constructor_term(cname, 0), do: {:ctor, cname, []}

  defp branch_constructor_term(cname, arity) do
    args = for i <- 0..(arity - 1), do: {:var, arity - 1 - i}
    {:ctor, cname, args}
  end

  # Extend the branch context with a constructor's argument telescope. The
  # telescope's type terms are written in the constructor's own isolated frame
  # `ctx_full = params ++ args`, so — mirroring the kernel's `extend_with_
  # telescope` — evaluate each against a local value environment seeded with the
  # scrutinee's actual parameter values (`param_vals`) beneath fresh neutrals for
  # the args already bound. A parameter reference in an arg type (e.g. `rest : a`
  # in `prepend`) then resolves to the scrutinee's parameter, not a stray outer
  # binder. Values carry absolute de Bruijn *levels*, so param_vals stay valid as
  # the context grows. For a parameter-free family this is the previous behavior.
  defp extend_context(ctx, telescope, param_vals) do
    {ctx_final, _local_vals} =
      Enum.reduce(telescope, {ctx, Enum.reverse(param_vals)}, fn {_name, type_term}, {c, local_vals} ->
        type_value = Eval.eval(type_term, local_vals)
        fresh_val = {:vneutral, {:nvar, Context.length(c)}}
        {Context.extend(c, type_value), [fresh_val | local_vals]}
      end)

    ctx_final
  end

  # Matching `xs : D i...` against a constructor whose result indices include a
  # direct telescope variable teaches the branch that this constructor variable
  # aliases the scrutinee's index. For Vec, `vcons : ... -> Vec(a, S(n))` in a
  # branch of `xs : Vec(a0, m)` gives `a := a0`; the `S(n) := m` refinement is
  # not invertible in this minimal pass, but the direct alias is enough for
  # `append(rest, ys)`.
  defp specialize_branch_context(ctx, result_indices, scrut_indices, arity) do
    subst = branch_index_subst(result_indices, scrut_indices, arity)

    if map_size(subst) == 0 do
      ctx
    else
      depth = Context.length(ctx)
      env = Context.env(ctx)

      types =
        Enum.map(ctx.types, fn type_value ->
          type_value
          |> Quote.reify(depth)
          |> replace_branch_vars(subst)
          |> Eval.eval(env)
        end)

      %{ctx | types: types}
    end
  end

  # Both `result_indices` (Task 6: ctor result stripped of its parameter prefix)
  # and `scrut_indices` (elaborate_match passes the index-only slice) are
  # index-only and equal-arity post param/index split, so they align head-to-head.
  defp branch_index_subst(result_indices, scrut_indices, arity) do
    result_indices
    |> Enum.zip(scrut_indices)
    |> Enum.reduce(%{}, fn
      {{:var, i}, scrut_idx}, acc ->
        Map.put(acc, i, Subst.shift(scrut_idx, arity, 0))

      {_other, _scrut_idx}, acc ->
        acc
    end)
  end

  defp replace_branch_vars({:var, i}, subst), do: Map.get(subst, i, {:var, i})

  defp replace_branch_vars({:pi, d, c}, subst),
    do: {:pi, replace_branch_vars(d, subst), replace_branch_vars(c, shift_subst(subst, 1))}

  defp replace_branch_vars({:lam, d, b}, subst),
    do: {:lam, replace_branch_vars(d, subst), replace_branch_vars(b, shift_subst(subst, 1))}

  defp replace_branch_vars({:sigma, a, b}, subst),
    do: {:sigma, replace_branch_vars(a, subst), replace_branch_vars(b, shift_subst(subst, 1))}

  defp replace_branch_vars({:app, f, a}, subst),
    do: {:app, replace_branch_vars(f, subst), replace_branch_vars(a, subst)}

  defp replace_branch_vars({:pair, a, b}, subst),
    do: {:pair, replace_branch_vars(a, subst), replace_branch_vars(b, subst)}

  defp replace_branch_vars({:fst, p}, subst), do: {:fst, replace_branch_vars(p, subst)}
  defp replace_branch_vars({:snd, p}, subst), do: {:snd, replace_branch_vars(p, subst)}

  defp replace_branch_vars({:data, n, ps, is}, subst),
    do: {:data, n, Enum.map(ps, &replace_branch_vars(&1, subst)), Enum.map(is, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:ctor, n, args}, subst),
    do: {:ctor, n, Enum.map(args, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:case, scr, m, brs}, subst),
    do:
      {:case, replace_branch_vars(scr, subst), replace_branch_vars(m, subst),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, replace_branch_vars(b, shift_subst(subst, ar))} end)}

  defp replace_branch_vars({:eq, t, a, b}, subst),
    do: {:eq, replace_branch_vars(t, subst), replace_branch_vars(a, subst), replace_branch_vars(b, subst)}

  defp replace_branch_vars({:refl, a}, subst), do: {:refl, replace_branch_vars(a, subst)}

  defp replace_branch_vars({:rewrite, p, m, b}, subst),
    do: {:rewrite, replace_branch_vars(p, subst), replace_branch_vars(m, subst), replace_branch_vars(b, subst)}

  defp replace_branch_vars({:prim, op, args}, subst),
    do: {:prim, op, Enum.map(args, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars(other, _subst), do: other

  defp shift_subst(subst, amount) do
    Map.new(subst, fn {k, v} -> {k + amount, Subst.shift(v, amount, 0)} end)
  end

  @doc """
  Elaborate a constructor application `C(a₁, …, aₙ)`, inferring the erased index
  arguments (quantity 0) from the runtime-relevant (quantity ω) arguments'
  types (design spec §5.2). `present_args` is `[{core_term, type_value}]` — the
  already-elaborated ω arguments with their inferred types.

  Fresh metavariables stand in for the erased arguments; each ω argument's
  expected telescope type is specialised with the choices so far (`Subst`) and
  unified against the provided argument's type (`Unify`). On success every
  metavariable is solved, and the fully-applied `{:ctor, …}` term plus its result
  type (the family at the computed indices) are returned.

  `present_args` is `[{core_term, type_term}]` — each ω argument with its type
  already reified as a term in the caller's de Bruijn frame.
  """
  @spec elaborate_ctor_app(Env.t(), atom(), [{term(), term()}]) ::
          {:ok, term(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate_ctor_app(env, cname, present_args) do
    ctor = Inductive.get_ctor(env, cname)
    family = Inductive.ctor_family(env, cname)

    if is_nil(ctor) or is_nil(family) do
      {:error, {:unknown_constructor, cname}}
    else
      # The family's parameters are bound outside the constructor's arg telescope
      # (the kernel checks it as `ctx_full = params ++ args`). A constructor arg
      # type — e.g. `prepend`'s `x : a` — can reference a parameter, so model the
      # parameters as leading erased slots: their metavariables are seeded into
      # the substitution frame and solved by unifying the present arguments. For
      # a parameter-free family this prefix is empty (unchanged behavior).
      param_tele = Inductive.param_telescope(env, family) || []
      param_slots = Enum.map(param_tele, fn entry -> {entry, :erased} end)
      telescope = param_slots ++ Enum.zip(ctor.args, ctor.quantities)
      init = {:ok, MetaCtx.new(), [], present_args}

      telescope
      |> Enum.reduce_while(init, &solve_arg/2)
      |> finish_ctor_app(cname, family, ctor, length(param_tele))
    end
  end

  # One telescope slot: erased → fresh meta; present → unify expected vs actual.
  defp solve_arg({{_name, _type_term}, :erased}, {:ok, mctx, chosen, present}) do
    {mctx, id} = MetaCtx.fresh(mctx)
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], present}}
  end

  defp solve_arg({{_name, _type_term}, :present}, {:ok, _mctx, _chosen, []}),
    do: {:halt, {:error, :too_few_arguments}}

  defp solve_arg({{_name, type_term}, :present}, {:ok, mctx, chosen, [{arg, arg_type_term} | rest]}) do
    expected = Subst.instantiate(type_term, chosen)

    case Unify.unify(expected, arg_type_term, mctx) do
      {:ok, mctx} -> {:cont, {:ok, mctx, chosen ++ [arg], rest}}
      {:error, reason} -> {:halt, {:error, {:index_mismatch, reason}}}
    end
  end

  defp finish_ctor_app({:error, _} = err, _cname, _family, _ctor, _pc), do: err

  defp finish_ctor_app({:ok, _mctx, _chosen, [_ | _]}, _cname, _family, _ctor, _pc),
    do: {:error, :too_many_arguments}

  defp finish_ctor_app({:ok, mctx, chosen, []}, cname, family, ctor, pc) do
    all = Enum.map(chosen, &Unify.zonk(&1, mctx))

    if Enum.any?(all, &has_meta?/1) do
      {:error, {:unsolved_metavariables, cname}}
    else
      # `chosen` is [solved parameters] ++ [constructor args]. The Core `:ctor`
      # term carries only the constructor args (parameters are erased and
      # recovered from the value's type); result params/indices reference
      # `ctx_full = params ++ args`, so instantiate them with the full frame.
      {param_vals, args} = Enum.split(all, pc)
      seed = param_vals ++ args
      params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
      indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))
      result_type = Eval.eval({:data, family, params, indices}, [])
      {:ok, {:ctor, cname, args}, result_type}
    end
  end

  # A saturated call to a global function with implicit (erased) parameters.
  # Peels the function's Π telescope, pairs each domain with its quantity, and
  # runs the shared `solve_arg` loop: erased slots become fresh metavariables,
  # present slots unify against the supplied arguments. Returns the applied term
  # and its result type (the codomain instantiated with the solved arguments).
  defp elaborate_global_app(env, name, present_args, ctx) do
    %{type: pi_type, quantities: quantities} = Env.get_def(env, name)
    {domains, codomain} = peel_pi(pi_type, length(quantities))

    telescope = Enum.zip(Enum.map(domains, &{:_, &1}), quantities)
    init = {:ok, MetaCtx.new(), [], present_args}

    telescope
    |> Enum.reduce_while(init, &solve_arg/2)
    |> finish_global_app(name, codomain, ctx)
  end

  defp peel_pi(type, 0), do: {[], type}

  defp peel_pi({:pi, d, c}, n) do
    {ds, co} = peel_pi(c, n - 1)
    {[d | ds], co}
  end

  defp finish_global_app({:error, _} = err, _name, _cod, _ctx), do: err

  defp finish_global_app({:ok, _mctx, _chosen, [_ | _]}, _name, _cod, _ctx),
    do: {:error, :too_many_arguments}

  defp finish_global_app({:ok, mctx, chosen, []}, name, codomain, ctx) do
    args = Enum.map(chosen, &Unify.zonk(&1, mctx))

    if Enum.any?(args, &has_meta?/1) do
      {:error, {:unsolved_metavariables, name}}
    else
      term = Enum.reduce(args, {:global, name}, fn a, acc -> {:app, acc, a} end)
      # The instantiated codomain lives in the caller's frame; evaluate it under
      # the caller's environment so its context variables get correct de Bruijn
      # levels (evaluating under `[]` would conflate index and level).
      result_type = Eval.eval(Subst.instantiate(codomain, args), Context.env(ctx))
      {:ok, term, result_type}
    end
  end

  defp has_meta?({:meta, _}), do: true
  defp has_meta?({:data, _n, ps, is}), do: Enum.any?(ps ++ is, &has_meta?/1)
  defp has_meta?({:ctor, _n, args}), do: Enum.any?(args, &has_meta?/1)
  defp has_meta?({:app, f, x}), do: has_meta?(f) or has_meta?(x)
  defp has_meta?(_), do: false

  # -- parameters / binders ---------------------------------------------------

  defp elaborate_params([], _scope, _env), do: {:ok, []}

  defp elaborate_params([{:param, pmeta, pname} | rest], scope, env) do
    with {:ok, ptype} <- elaborate_type(Keyword.fetch!(pmeta, :type), scope, env),
         {:ok, more} <- elaborate_params(rest, [pname | scope], env) do
      {:ok, [{pname, ptype} | more]}
    end
  end

  # Wrap a Core body in λ's (or Π's) over the parameter telescope, p0 outermost.
  defp wrap(tag, tele, body) do
    Enum.reduce(Enum.reverse(tele), body, fn {_name, type}, acc -> {tag, type, acc} end)
  end

  defp single_body([expr]), do: expr
  defp single_body(expr), do: expr

  # -- expressions ------------------------------------------------------------

  @doc false
  def elaborate_expr({:variable, _meta, "Type"}, _scope, _env), do: {:ok, {:type, 0}}

  def elaborate_expr({:variable, _meta, name}, scope, env) do
    case Enum.find_index(scope, &(&1 == name)) do
      nil -> resolve_free(name, env)
      index -> {:ok, {:var, index}}
    end
  end

  def elaborate_expr({:function_call, meta, args}, scope, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    with {:ok, core_args} <- map_elaborate(args, scope, env, &elaborate_expr/3) do
      if Inductive.get_ctor(env, atom) do
        # A constructor head applied to arguments is a saturated constructor, not
        # a chain of `{:app, …}`. Mirror `elaborate_type/3`'s ctor-aware clause:
        # `resolve_free` only ever yields the NULLARY `{:ctor, atom, []}`, so
        # folding args on with `{:app, …}` would apply a nullary ctor to an
        # argument and the kernel would reject it (`:ctor_arity`).
        {:ok, {:ctor, atom, core_args}}
      else
        with {:ok, head} <- elaborate_expr({:variable, [], name}, scope, env) do
          {:ok, Enum.reduce(core_args, head, fn arg, acc -> {:app, acc, arg} end)}
        end
      end
    end
  end

  def elaborate_expr(other, _scope, _env), do: {:error, {:unsupported_expression, other}}

  # A free name is a nullary constructor, a global definition, or (fallback) a global ref.
  defp resolve_free(name, env) do
    atom = String.to_atom(name)

    cond do
      Inductive.get_ctor(env, atom) -> {:ok, {:ctor, atom, []}}
      Inductive.family?(env, atom) -> {:ok, {:data, atom, [], []}}
      true -> {:ok, {:global, atom}}
    end
  end

  # -- type expressions -------------------------------------------------------

  defp elaborate_type({:variable, _meta, "Type"}, _scope, _env), do: {:ok, {:type, 0}}

  defp elaborate_type({:variable, _meta, name}, scope, _env) do
    case Enum.find_index(scope, &(&1 == name)) do
      nil -> {:ok, {:data, String.to_atom(name), [], []}}
      index -> {:ok, {:var, index}}
    end
  end

  defp elaborate_type({:function_call, meta, args}, scope, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()

    with {:ok, core_args} <- map_elaborate(args, scope, env, &elaborate_type/3) do
      {:ok, {:data, name, [], core_args}}
    end
  end

  defp elaborate_type(other, _scope, _env), do: {:error, {:unsupported_type, other}}

  # -- helpers ----------------------------------------------------------------

  defp map_elaborate(asts, scope, env, fun) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case fun.(ast, scope, env) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
