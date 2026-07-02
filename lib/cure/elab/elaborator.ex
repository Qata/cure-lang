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
    cond do
      # Record construction `Point{x: .., y: ..}` desugars to the positional
      # constructor `Point(.., ..)` (fields ordered by the record's telescope).
      Keyword.get(meta, :record) ->
        with {:ok, positional} <- desugar_record_construction(meta, args, env) do
          elaborate_expr_typed(positional, names, ctx, env)
        end

      # `f(x)(y)` parses with the inner call preserved as `:callee` (and `name`
      # left "unknown"): elaborate the callee expression, then apply the outer
      # arguments to its (function-typed) result.
      callee = Keyword.get(meta, :callee) ->
        with {:ok, head, head_type} <- elaborate_expr_typed(callee, names, ctx, env) do
          check_app_args(head, head_type, args, names, ctx, env)
        end

      true ->
        elaborate_named_call(meta, args, names, ctx, env)
    end
  end

  # Desugar record construction `Point{x: .., y: ..}` (a `record: true` call whose
  # arguments are `field: value` pairs) into the positional constructor application
  # `Point(.., ..)`, ordering the values by the record constructor's field telescope
  # (the constructor's argument names ARE the field names). Missing or extra fields
  # are rejected.
  defp desugar_record_construction(meta, field_pairs, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    case Inductive.get_ctor(env, atom) do
      nil ->
        {:error, {:unknown_record, atom}}

      ctor ->
        order = Enum.map(ctor.args, fn {n, _t} -> n end)
        provided = Map.new(field_pairs, fn {:pair, _m, [{:literal, _s, f}, val]} -> {f, val} end)

        if map_size(provided) == length(order) and
             Enum.all?(order, &Map.has_key?(provided, &1)) do
          {:ok, {:function_call, [name: name], Enum.map(order, &Map.fetch!(provided, &1))}}
        else
          {:error, {:record_field_mismatch, atom}}
        end
    end
  end

  defp elaborate_named_call(meta, args, names, ctx, env) do
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
          elaborate_ctor_app(env, atom, present, ctx)
        end

      # A global whose telescope carries erased (implicit) parameters: insert
      # fresh metavariables for them and solve from the present arguments, the
      # same way constructor indices are inferred (§5.2). Without this, the
      # explicit args would be bound to the implicit positions.
      implicit_def?(env, atom) ->
        with {:ok, present} <- map_present_args(args, names, ctx, env) do
          elaborate_global_app(env, atom, present, ctx)
        end

      # A call carrying a lambda argument needs the callee's parameter types to
      # reach the (untyped-in-surface) lambda: elaborate bidirectionally, checking
      # each argument against its Π domain. Restricted to lambda-bearing calls so
      # every other application keeps its exact existing inference path.
      Enum.any?(args, &match?({:lambda, _m, _b}, &1)) ->
        elaborate_bidirectional_app(name, args, names, ctx, env)

      true ->
        # Non-constructor application: elaborate to a term, then let the kernel type it.
        with {:ok, term} <- elaborate_expr({:function_call, [name: name], args}, names, env),
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end
    end
  end

  # Saturated application checked argument-by-argument against the callee's Π
  # telescope, so a lambda argument is elaborated in checking mode (its parameter
  # types come from the domain). The codomain is instantiated at each argument's
  # value, so a dependent parameter type is honoured too.
  defp elaborate_bidirectional_app(name, args, names, ctx, env) do
    with {:ok, head} <- elaborate_expr({:variable, [], name}, names, env),
         {:ok, head_type} <- Kernel.infer(ctx, head) do
      check_app_args(head, head_type, args, names, ctx, env)
    end
  end

  defp check_app_args(term, type, [], _names, _ctx, _env), do: {:ok, term, type}

  defp check_app_args(term, type, [arg | rest], names, ctx, env) do
    case type do
      {:vpi, dom_value, cod_closure} ->
        dom_term = Quote.reify(dom_value, Context.length(ctx))

        with {:ok, arg_term} <- elaborate_expr_checked(arg, dom_term, names, ctx, env) do
          arg_value = Eval.eval(arg_term, Context.env(ctx))
          next_type = Eval.apply_closure(cod_closure, arg_value)
          check_app_args({:app, term, arg_term}, next_type, rest, names, ctx, env)
        end

      _ ->
        {:error, :applied_non_function}
    end
  end

  # Projection of a literal pair reduces by the Σ β-rule (`fst %[a,b] = a`,
  # `snd %[a,b] = b`), so we take the component directly — no `{:pair, …}` is built
  # and the kernel is never asked to infer a bare pair. This is what makes a
  # let-bound pair work: `let p = %[a, b]` is substitution-based, so `p.1`/`p.2`
  # become `%[a, b].1`/`.2` after inlining.
  def elaborate_expr_typed({:attribute_access, meta, [{:tuple, _tm, [a, b]}]} = expr, names, ctx, env) do
    case Keyword.fetch!(meta, :attribute) do
      "1" -> elaborate_expr_typed(a, names, ctx, env)
      "2" -> elaborate_expr_typed(b, names, ctx, env)
      _ -> {:error, {:unsupported_expression, expr}}
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
  def elaborate_expr_checked({:function_call, meta, args} = expr, expected_core, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    cond do
      Keyword.get(meta, :record) ->
        with {:ok, positional} <- desugar_record_construction(meta, args, env) do
          elaborate_expr_checked(positional, expected_core, names, ctx, env)
        end

      name == "refl" and length(args) == 1 ->
        [arg] = args

        with {:ok, arg_term, _type} <- elaborate_expr_typed(arg, names, ctx, env),
             term = {:refl, arg_term},
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      Inductive.get_ctor(env, atom) ->
        # Checking-mode constructor: pin erased indices from the expected type (a
        # reconstructed dependent-match branch body like `prim()`/`seq(l,r)` whose
        # indices no present argument determines), then let the kernel re-check the
        # assembled constructor against the goal.
        with {:ok, present} <- map_present_args(args, names, ctx, env),
             {:ok, term, _type} <- elaborate_ctor_app(env, atom, present, ctx, expected_core),
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      true ->
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
         {:ok, build, body_expected} <- rewrite_plan(ctx, proof_term, ty, a, b, normalized_expected),
         {:ok, body_term} <- elaborate_expr_checked(body_ast, body_expected, names, ctx, env),
         term = build.(body_term),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  # A `match` in nested expression position, in checking mode: the expected type
  # IS the result type its motive needs, so hand it straight to `elaborate_match`
  # (which builds the motive, refines indices per branch, and enforces coverage),
  # then let the kernel re-check the assembled `:case` — mirroring `:rewrite_expr`
  # above. Reached from `rewrite … in match …` (line ~151) and from nested arm
  # bodies (`elaborate_branch_body`). `let`-blocks are now handled in checking
  # mode (the `{:block, …}` clause below); inference-position inline match (no
  # expected type) stays unimplemented (a separate aux-function lift).
  def elaborate_expr_checked({:pattern_match, _meta, [scrut | arms]}, expected_core, names, ctx, env) do
    with {:ok, term} <- elaborate_match(scrut, arms, expected_core, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  # A `let x = e ⏎ body` block, in checking mode. There is no `:let` in Core, so
  # each binding desugars to a β-redex `(λ x:T. body) e`: infer the rhs, extend
  # the context with `x : T`, check the remainder against the expected type
  # shifted under the new binder, and wrap. The kernel re-checks the assembled
  # redex against the expected type.
  def elaborate_expr_checked({:block, _meta, stmts}, expected_core, names, ctx, env) do
    elaborate_let_block(stmts, expected_core, names, ctx, env)
  end

  # Dependent-pair introduction `%[a, b]` in checking mode. The expected type must
  # be a Σ; elaborate `a` against its domain, then `b` against the codomain
  # instantiated at `a` (so a component like `prim()` gets its erased indices from
  # the expected `SF(as, bs, d)`, not left as unsolved metavariables). The kernel
  # re-checks the assembled `{:pair, …}`.
  def elaborate_expr_checked({:tuple, _meta, [a_ast, b_ast]} = expr, expected_core, names, ctx, env) do
    case Kernel.normalize(ctx, expected_core) do
      {:sigma, dom, cod} ->
        with {:ok, a_term} <- elaborate_expr_checked(a_ast, dom, names, ctx, env),
             cod_inst = Subst.instantiate(cod, [a_term]),
             {:ok, b_term} <- elaborate_expr_checked(b_ast, cod_inst, names, ctx, env),
             term = {:pair, a_term, b_term},
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      _ ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
    end
  end

  # Lambda in checking mode: the expected type supplies the parameter types the
  # surface leaves untyped. `fn(a, b) -> body` against `Π a. Π b. C` curries to
  # `λa. λb. body` — each parameter is bound at the corresponding domain and the
  # body checked against the final codomain. A lambda needs a known Π (Idris
  # likewise only *checks*, never *infers*, an unannotated lambda); one in an
  # inference position (e.g. a bare higher-order argument) still needs the
  # expected type routed to it, which is a separate bidirectional-application step.
  def elaborate_expr_checked({:lambda, meta, [body_expr]}, expected_core, names, ctx, env) do
    with {:ok, term} <-
           elaborate_lambda(Keyword.fetch!(meta, :params), body_expr, expected_core, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  def elaborate_expr_checked(expr, expected_core, names, ctx, env),
    do: elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

  defp elaborate_lambda([], body_expr, expected_core, names, ctx, env),
    do: elaborate_expr_checked(body_expr, expected_core, names, ctx, env)

  defp elaborate_lambda([{:param, _pm, pname} | rest], body_expr, expected_core, names, ctx, env) do
    case Kernel.normalize(ctx, expected_core) do
      {:pi, dom_term, cod_term} ->
        dom_value = Eval.eval(dom_term, Context.env(ctx))
        ctx1 = Context.extend(ctx, dom_value)

        with {:ok, body_term} <-
               elaborate_lambda(rest, body_expr, cod_term, [pname | names], ctx1, env) do
          {:ok, {:lam, dom_term, body_term}}
        end

      _ ->
        {:error, {:lambda_expected_pi, expected_core}}
    end
  end

  defp elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env) do
    with {:ok, term, _type} <- elaborate_expr_typed(expr, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  defp eq_parts({:veq, ty, a, b}), do: {:ok, ty, a, b}
  defp eq_parts(_other), do: {:error, :rewrite_proof_not_equality}

  # Plan a `rewrite p in t` whose proof `p : Eq(ty, a, b)` transports along the
  # goal `expected`. Returns `{:ok, build, body_expected}`: `body_expected` is
  # the goal the surface body `t` must satisfy, and `build.(body_core)` assembles
  # the full Core `:rewrite` term(s) around the checked body. (A builder — rather
  # than a fixed `proof`/`motive` pair — lets the bridge case below nest an outer
  # rewrite around the original one.)
  #
  # Core rewrite transports M[a] -> M[b]. Idris-style source `rewrite p in t`
  # checks `t` under the rewritten goal and returns the original goal, so when
  # the expected type contains the proof's left endpoint we synthesize symmetry.
  defp rewrite_plan(ctx, proof, ty, a, b, expected) do
    cond do
      contains_term?(expected, a) ->
        with {:ok, sym_proof} <- symmetry_proof(proof, ty, a, b),
             {:ok, motive} <- motive_for(expected, a, ty) do
          {:ok, fn body -> {:rewrite, sym_proof, motive, body} end, replace_term(expected, a, b)}
        end

      # Definitional-but-not-syntactic occurrence (P0, rw07): `a` is absent from
      # the goal syntactically, but a δ-reducible sub-occurrence of the goal
      # normalizes at top level to a form that *exposes* `a`. Bridge it — see
      # `bridge_step/7` — instead of falling through to the (wrong) `b` branch.
      bridge = find_bridge(ctx, expected, a) ->
        bridge_step(ctx, proof, ty, a, b, expected, bridge)

      contains_term?(expected, b) ->
        {:ok, motive} = motive_for(expected, b, ty)
        {:ok, fn body -> {:rewrite, proof, motive, body} end, replace_term(expected, b, a)}

      true ->
        {:error, {:rewrite_no_match, a, b, expected}}
    end
  end

  # Bridge-lemma rewrite step (P0 rw07, elaborator-only — no TCB change).
  #
  # The trusted normalizer preserves stuck `case`s and never δ-reduces the
  # scrutinee, so a goal like `Eq(Nat, plus(plus(Z,n),Z), n)` freezes with the
  # sub-term `plus(Z,n)` unreduced in scrutinee position; the proof's endpoint
  # `plus(n,Z)` is therefore only *definitionally* (not syntactically) present
  # and the syntactic occurrence match misses. The kernel cannot be asked to
  # decide that conversion (its scrutinee stays stuck), but the *sub-occurrence*
  # `plus(Z,n)` reduces to `n` at TOP level, a conversion the kernel does decide.
  #
  # We turn that top-level definitional step into an explicit propositional
  # rewrite. The OUTER rewrite transports along an inline refl-bodied bridge
  # proof of `Eq(ty_s, s', s)`; its residual goal is `expected` with `s` reduced
  # to `s'`, which now contains `a` syntactically — so the ORIGINAL rewrite
  # (recursively planned at that residual, the already-working `a`-branch) is
  # nested as its body. Every conversion the kernel then sees is either
  # top-level-decidable or between structurally identical terms.
  #
  # Scope (honest): this closes the reducible-inner-occurrence pattern rw07
  # exercises — a single sub-occurrence whose top-level normal form exposes the
  # proof endpoint. It does NOT implement fully general up-to-conversion
  # occurrence matching.
  defp find_bridge(ctx, expected, a) do
    expected
    |> reducible_subterms()
    |> Enum.find_value(fn s ->
      s_nf = Kernel.normalize(ctx, s)
      if s_nf != s and contains_term?(replace_term(expected, s, s_nf), a) do
        {s, s_nf}
      end
    end)
  end

  defp bridge_step(ctx, proof, ty, a, b, expected, {s, s_nf}) do
    with {:ok, ty_s} <- infer_type_term(ctx, s),
         residual = replace_term(expected, s, s_nf),
         {:ok, inner_build, body_expected} <- rewrite_plan(ctx, proof, ty, a, b, residual) do
      # Inline bridge proof `Eq(ty_s, s', s)`: the outer `rewrite` (its proof)
      # infers this asymmetric equality via a constant motive `λ_. Eq(ty_s, s', s)`
      # whose `refl s'` premise is *checked* against `Eq(ty_s, s', s)` — the
      # top-level conversion `s' ≡ s` the kernel decides. (A bare `refl` in proof
      # position would only *infer* the symmetric `Eq(ty_s, s', s')`.)
      const_motive =
        {:lam, ty_s,
         {:eq, Subst.shift(ty_s, 1, 0), Subst.shift(s_nf, 1, 0), Subst.shift(s, 1, 0)}}

      bridge_proof = {:rewrite, {:refl, s_nf}, const_motive, {:refl, s_nf}}
      {:ok, outer_motive} = motive_for(expected, s, ty_s)

      build = fn body ->
        {:rewrite, bridge_proof, outer_motive, inner_build.(body)}
      end

      {:ok, build, body_expected}
    end
  end

  # Global-headed applications occurring in `term` (outermost-first): the only
  # sub-terms the trusted normalizer may δ-reduce, hence the bridge candidates.
  defp reducible_subterms(term) do
    here = if global_app?(term), do: [term], else: []
    here ++ Enum.flat_map(children(term), &reducible_subterms/1)
  end

  defp global_app?({:app, f, _}), do: global_head?(f)
  defp global_app?(_), do: false
  defp global_head?({:global, _}), do: true
  defp global_head?({:app, f, _}), do: global_head?(f)
  defp global_head?(_), do: false

  defp infer_type_term(ctx, term) do
    with {:ok, ty_value} <- Kernel.infer(ctx, term) do
      {:ok, Quote.reify(ty_value, Context.length(ctx))}
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

  # Free de Bruijn indices in `term`, counted from `depth` binders in (binder-
  # aware for Π/λ/Σ/case, mirroring abstract_term). Used to check convoy sibling
  # independence.
  defp free_indices({:var, i}, depth) when i >= depth, do: MapSet.new([i - depth])
  defp free_indices({:var, _}, _depth), do: MapSet.new()

  defp free_indices({:pi, d, c}, depth),
    do: MapSet.union(free_indices(d, depth), free_indices(c, depth + 1))

  defp free_indices({:lam, d, b}, depth),
    do: MapSet.union(free_indices(d, depth), free_indices(b, depth + 1))

  defp free_indices({:sigma, a, b}, depth),
    do: MapSet.union(free_indices(a, depth), free_indices(b, depth + 1))

  defp free_indices({:case, s, m, brs}, depth) do
    base = MapSet.union(free_indices(s, depth), free_indices(m, depth))
    Enum.reduce(brs, base, fn {_c, ar, b}, acc -> MapSet.union(acc, free_indices(b, depth + ar)) end)
  end

  defp free_indices(term, depth) when is_tuple(term),
    do: term |> children() |> Enum.reduce(MapSet.new(), &MapSet.union(&2, free_indices(&1, depth)))

  defp free_indices(term, depth) when is_list(term),
    do: Enum.reduce(term, MapSet.new(), &MapSet.union(&2, free_indices(&1, depth)))

  defp free_indices(_term, _depth), do: MapSet.new()

  # Largest free de Bruijn index occurring anywhere in `terms` (−1 if none). Used
  # to pick sentinel variables for computed-index abstraction that are guaranteed
  # not to alias any existing variable.
  defp max_free_ref(terms) do
    terms
    |> Enum.reduce(MapSet.new(), fn t, acc -> MapSet.union(acc, free_indices(t, 0)) end)
    |> MapSet.to_list()
    |> Enum.max(fn -> -1 end)
  end

  # `Quote.reify` collapses a `{:vdata, name, params ++ indices}` value into
  # `{:data, name, all_args, []}` (the value rep does not track the param/index
  # split). Restore the split for every data application in `term` using the
  # family's declared param count, so the kernel's `:data` rule — which checks
  # params and indices against separate telescopes — accepts reified sibling and
  # transport types.
  defp resplit_data({:data, name, params, indices}, env) do
    combined = Enum.map(params ++ indices, &resplit_data(&1, env))
    {ps, is} = Enum.split(combined, Inductive.param_count(env, name))
    {:data, name, ps, is}
  end

  defp resplit_data(term, env) when is_tuple(term),
    do: rebuild(term, Enum.map(children(term), &resplit_data(&1, env)))

  defp resplit_data(term, env) when is_list(term),
    do: Enum.map(term, &resplit_data(&1, env))

  defp resplit_data(term, _env), do: term

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
  def elaborate_match(scrut_expr, arms0, result_type_term, names, ctx, env) do
    with {:ok, arms1} <- desugar_as_patterns(arms0),
         {:ok, arms1b} <- desugar_tuple_args(arms1),
         {:ok, arms} <- desugar_nested_arms(arms1b, scrut_expr),
         :not_applicable <- try_tuple_match(scrut_expr, arms, result_type_term, names, ctx, env),
         {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env),
         :not_applicable <-
           try_trivial_match(scrut_expr, arms, result_type_term, names, ctx, env) do
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

          motive0 =
            build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)

          # Step 3b: a *sibling* whose type mentions the scrutinee's stuck computed
          # index (`w : F(app(p,q))`) is not refined by 3a's motive (that only
          # generalizes the scrutinee's own goal). Carry `Eq(T, app(p,q), jₚₒₛ)`
          # into the motive and transport each such sibling in the branch body —
          # the same kernel-checked Eq-arrow + `rewrite` vehicle as capability B,
          # lifted from the scrutinee VALUE to its computed INDEX term.
          carried = detect_carried_index(family.indices, idx_terms, scrut_term, names, ctx, env)
          k = length(family.indices)
          motive = if carried, do: wrap_motive_carried_eq(motive0, k, carried), else: motive0

          with {:ok, branches} <-
                 elaborate_branches(
                   arms, names, ctx, env, dname,
                   idx_vals, param_vals, scrut_term, result_type_term, carried
                 ) do
            case_term = {:case, scrut_term, motive, branches}
            {:ok, if(carried, do: {:app, case_term, {:refl, carried.idx_term}}, else: case_term)}
          end

        _ ->
          {:error, :match_scrutinee_not_data}
      end
    end
  end

  @doc """
  Elaborate a surface `with <scrut> [proof <name>] | C(pat…) -> body …` into a
  Core `:case`. Unlike `elaborate_match`, the motive is *value-abstracting*: the
  scrutinee EXPRESSION is abstracted out of the goal (`motive_for`-style), so
  each branch's expected type is the goal with the scrutinee replaced by that
  branch's constructor value — goal refinement that plain `match` cannot do (its
  `build_motive` only generalizes type INDICES).

  Capabilities A (goal refinement), B (`proof <name>`), and sibling/other-
  argument refinement share ONE Eq-arrow mechanism. Let `e : T`, goal `G`, and
  the SIBLINGS be the in-scope parameters `h_j : H_j` whose type mentions `e`.
  When either a proof clause or a sibling is present, the motive carries the
  scrutinee equation:

      motive = λ(w:T). Eq(T, e, w) -> G[e↦w]
      term   = (case e of … branches …) (refl e)   : G

  and each branch receives `prf : Eq(T, e, pat)` (the user's proof name, or an
  internal one). Siblings are refined **by transport in the branch body**, NOT
  by generalizing their type into the motive (a `Π(SNat(w))…` motive domain
  trips `Quote.reify`'s `{:vdata}` param/index collapse — a real kernel gap,
  reach-pinned separately). For each sibling:

      h_j' = rewrite prf (λx. H_j[e↦x]) h_j   : H_j[e↦pat]

  bound in the arm body via `(λ h_j'. body) h_j'`, so the ORIGINAL name resolves
  to the refined `h_j'`. The indexed-data type only ever appears as a `:rewrite`
  motive RESULT (which the kernel `Eval.apply`s, never reifies) — sound, no TCB.
  Capability A is the no-equation special case (bare value-abstracting motive).
  Restricted to a non-indexed scrutinee family; this slice generalizes only
  siblings that form an independent set (see `collect_with_siblings`).
  """
  @spec elaborate_with(term(), [tuple()], String.t() | nil, term(), [String.t()], Context.t(), Env.t(), [tuple()]) ::
          {:ok, term()} | {:error, term()}
  def elaborate_with(scrut_expr, arms, proof_name, result_type_term, names, ctx, env, original_params \\ []) do
    cond do
      Enum.any?(arms, &with_rematch_arm?/1) ->
        if Enum.all?(arms, &with_rematch_arm?/1) do
          elaborate_with_rematch(scrut_expr, arms, original_params, result_type_term, names, ctx, env)
        else
          {:error, :with_mixed_rematch_arms}
        end

      true ->
        elaborate_with_value(scrut_expr, arms, proof_name, result_type_term, names, ctx, env)
    end
  end

  defp with_rematch_arm?({:with_rematch_arm, _, _}), do: true
  defp with_rematch_arm?(_), do: false

  # Capability A/B (no LHS re-match): value-abstracting motive + eq-arrow sibling
  # transport, restricted to a NON-indexed scrutinee family. This is the original
  # `elaborate_with` body, unchanged.
  defp elaborate_with_value(scrut_expr, arms, proof_name, result_type_term, names, ctx, env) do
    with {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)

          if family.indices == [] do
            pc = Inductive.param_count(env, dname)
            {param_vals, _idx_vals} = Enum.split(combined_vals, pc)
            scrut_type_term = resplit_data(Quote.reify(scrut_type, Context.length(ctx)), env)

            with {:ok, siblings} <- collect_with_siblings(scrut_term, names, ctx, env) do
              # An Eq-arrow is needed when the user asked for a proof OR when a
              # sibling must be transported (both consume `prf : Eq(T,e,pat)`).
              need_eq = proof_name != nil or siblings != []

              if need_eq do
                # Capability B (proof / sibling transport) — the Eq-arrow motive.
                g_abs = abstract_term(result_type_term, scrut_term, 0)
                motive = eq_arrow_motive(scrut_type_term, scrut_term, g_abs)

                cfg = %{
                  names: names,
                  ctx: ctx,
                  env: env,
                  dname: dname,
                  param_vals: param_vals,
                  motive: motive,
                  need_eq: true,
                  siblings: siblings,
                  prf_name: proof_name || "$with_prf",
                  scrut_term: scrut_term,
                  scrut_type_term: scrut_type_term
                }

                with {:ok, branches} <- elaborate_with_branches(arms, cfg) do
                  case_term = {:case, scrut_term, motive, branches}
                  {:ok, {:app, case_term, {:refl, scrut_term}}}
                end
              else
                # Capability A (bare value-abstraction) is SUBSUMED by the unified
                # match front-end: since Phase 2½ plain `match` value-refines the
                # goal per branch (the same refinement A's `{:lam, T, g_abs}` motive
                # provided), so `with <e>` with no proof and no sibling is exactly a
                # plain `match <e>`. (Task 3.2; the arms are already `{:match_arm}`.)
                elaborate_match(scrut_expr, arms, result_type_term, names, ctx, env)
              end
            end
          else
            {:error, {:with_indexed_scrutinee_unsupported, dname}}
          end

        _ ->
          {:error, :with_scrutinee_not_data}
      end
    end
  end

  # -- LHS re-match over an indexed view (Idris-parity indexed views) ----------
  #
  # A with-clause that restates the parent LHS (`{:with_rematch_arm}`) is
  # elaborated like an indexed `match` — NOT the value-abstracting capability-A
  # path. The scrutinee (e.g. `view n : NV n`) is genuinely indexed; the goal is
  # generalized over its index variables by `build_motive`, and each branch is
  # refined by the kernel's index inversion (`branch_unify` yields `n := S(m)`).
  # That SAME substitution refines the branch goal AND every index-mentioning
  # sibling (e.g. `w : SNat n` ↦ `SNat (S m)`) via `specialize_branch_context`.
  # The kernel independently re-checks the assembled `{:case,…}`, so the
  # refinement is sound with no TCB change (the index equation comes from the
  # case eliminator, not from an index-injectivity assumption). `match_parent_lhs`
  # validates each restated LHS is constructor-refined (rejecting forced/
  # arithmetic patterns — the deferred #5 case) before the arm is admitted.
  defp elaborate_with_rematch(scrut_expr, arms, original_params, result_type_term, names, ctx, env) do
    with {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)
          pc = Inductive.param_count(env, dname)
          {param_vals, idx_vals} = Enum.split(combined_vals, pc)
          depth = Context.length(ctx)
          param_terms = Enum.map(param_vals, &Quote.reify(&1, depth))
          idx_terms = Enum.map(idx_vals, &Quote.reify(&1, depth))

          motive =
            build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)

          with {:ok, arm_map} <- partition_rematch_arms(arms, original_params, ctx, env, dname),
               {:ok, branches} <-
                 elaborate_rematch_branches(
                   arm_map, names, ctx, env, dname, idx_vals, param_vals, scrut_term, result_type_term
                 ) do
            {:ok, {:case, scrut_term, motive, branches}}
          end

        _ ->
          {:error, :with_scrutinee_not_data}
      end
    end
  end

  # Build `cname => {:matched, with_pattern, body} | {:impossible_marked, ...}`,
  # validating (a) the with-pattern names one of dname's OWN constructors (reused
  # from `partition_arms` semantics), and (b) the restated parent patterns are a
  # legal LHS re-match of `original_params` (`match_parent_lhs`) — the point at
  # which a forced/arithmetic restated pattern (`k+k`) is rejected.
  defp partition_rematch_arms(arms, original_params, ctx, env, dname) do
    sig = Context.signature(ctx)

    Enum.reduce_while(arms, {:ok, %{}}, fn {:with_rematch_arm, arm_meta, body}, {:ok, acc} ->
      with_pattern = Keyword.fetch!(arm_meta, :pattern)
      parent_patterns = Keyword.fetch!(arm_meta, :parent_patterns)

      with {:ok, {cname, _vars}} <- constructor_pattern(with_pattern),
           {:ok, _subst} <- match_parent_lhs(original_params, parent_patterns) do
        cond do
          Inductive.get_ctor(env, cname) == nil ->
            {:halt, {:error, {:unknown_pattern_constructor, cname}}}

          Inductive.ctor_family(sig, cname) != dname ->
            {:halt, {:error, {:foreign_ctor, cname}}}

          Map.has_key?(acc, cname) ->
            {:halt, {:error, {:duplicate_branch, cname}}}

          true ->
            {:cont, {:ok, Map.put(acc, cname, {:matched, with_pattern, single_body(body)})}}
        end
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # One Core branch per declared constructor (coverage), mirroring
  # `elaborate_branches`: an omitted/impossible constructor is discharged with
  # `{:absurd}`; a matched constructor's body is elaborated under the kernel's
  # index-refinement substitution.
  defp elaborate_rematch_branches(arm_map, names, ctx, env, dname, idx_vals, param_vals, scrut_term, result_type_term) do
    sig = Context.signature(ctx)

    sig
    |> Inductive.ctors_of(dname)
    |> Enum.map(& &1.name)
    |> Enum.reduce_while({:ok, []}, fn cname, {:ok, acc} ->
      verdict = Kernel.branch_unify(ctx, dname, cname, idx_vals)

      case Map.get(arm_map, cname) do
        {:matched, with_pattern, body_expr} ->
          case elaborate_rematch_branch(
                 verdict, cname, with_pattern, body_expr, names, ctx, env,
                 param_vals, scrut_term, result_type_term
               ) do
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end

        nil ->
          if verdict == :impossible do
            {arity, _} = ctor_arity(env, cname)
            {:cont, {:ok, acc ++ [{cname, arity, {:absurd}}]}}
          else
            {:halt, {:error, {:missing_branch, cname}}}
          end
      end
    end)
  end

  defp elaborate_rematch_branch(verdict, cname, with_pattern, body_expr, names, ctx, env, param_vals, scrut_term, result_type_term) do
    {:ok, {^cname, pattern_vars}} = constructor_pattern(with_pattern)
    %{args: telescope, quantities: quantities} = Inductive.get_ctor(env, cname)
    arity = length(telescope)
    branch_names = branch_scope(quantities, pattern_vars) ++ names

    case verdict do
      :impossible ->
        {:ok, {cname, arity, {:absurd}}}

      _solved_or_trivial ->
        subst =
          case verdict do
            {:solved, s} -> s
            :trivial -> %{}
          end

        # The index inversion (`n := S(m)`) refines the branch goal AND every
        # index-mentioning sibling in the context.
        branch_ctx =
          ctx
          |> extend_context(telescope, param_vals)
          |> specialize_branch_context_subst(subst)

        # Compose (1b) value-refinement with (1a) index inversion via the shared
        # `refine_branch_goal` (Task 3.4) — the SAME refinement plain match uses.
        # The rematch path abstracts the computed scrutinee in the MOTIVE (shared
        # `build_motive`); this refines the branch goal to the constructor too.
        branch_expected =
          refine_branch_goal(result_type_term, scrut_term, cname, arity, subst, branch_ctx)

        body_expr = refine_scrutinee_in_body(body_expr, scrut_term, with_pattern, pattern_vars, names)

        with {:ok, body_term} <-
               elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
          {:ok, {cname, arity, body_term}}
        end
    end
  end

  # Refine every context type by a branch substitution (kernel-frame de Bruijn
  # keys), mirroring the kernel's `specialize_branch_context`: reify → replace →
  # re-eval (the reify/eval round-trip repairs the flat-`{:vdata}` split).
  defp specialize_branch_context_subst(ctx, subst) when map_size(subst) == 0, do: ctx

  defp specialize_branch_context_subst(ctx, subst) do
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

  # Eq-arrow motive `λ(w:T). Eq(T, e, w) -> G[e↦w]`. Under the `w`-binder, `e`/`T`
  # shift by +1; `g_abs` (= `G[e↦w]`, already under one binder) shifts +1 more to
  # clear the extra Eq-arrow (proof) binder.
  defp eq_arrow_motive(scrut_type_term, scrut_term, g_abs) do
    eq_ty_w =
      {:eq, Subst.shift(scrut_type_term, 1, 0), Subst.shift(scrut_term, 1, 0), {:var, 0}}

    {:lam, scrut_type_term, {:pi, eq_ty_w, Subst.shift(g_abs, 1, 0)}}
  end

  # In-scope parameters whose (reified) type mentions the scrutinee term, in
  # scope order (outermost binder first). STOPs (rather than mis-building) when a
  # generalized sibling's type mentions another generalized sibling, or a kept
  # parameter depends on a generalized one — this slice handles only an
  # independent set.
  defp collect_with_siblings(scrut_term, names, ctx, env) do
    depth = Context.length(ctx)

    gen =
      names
      |> Enum.with_index()
      |> Enum.flat_map(fn {name, i} ->
        if is_binary(name) do
          type_term = resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env)

          if contains_term?(type_term, scrut_term),
            do: [%{name: name, index: i, type_term: type_term}],
            else: []
        else
          []
        end
      end)
      |> Enum.sort_by(& &1.index, :desc)

    gen_set = gen |> Enum.map(& &1.index) |> MapSet.new()

    cond do
      Enum.any?(gen, fn %{type_term: t, index: idx} ->
        not MapSet.disjoint?(free_indices(t, 0), MapSet.delete(gen_set, idx))
      end) ->
        {:error, {:with_sibling_dependency_unsupported, :sibling_references_sibling}}

      Enum.any?(0..(depth - 1)//1, fn i ->
        not MapSet.member?(gen_set, i) and
          not MapSet.disjoint?(
            free_indices(resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env), 0),
            gen_set
          )
      end) ->
        {:error, {:with_sibling_dependency_unsupported, :kept_references_sibling}}

      true ->
        {:ok, gen}
    end
  end

  # Emit one Core branch per surface arm. Reuses partition_arms (same validation
  # as match: own-family ctors, no duplicates). A `-> impossible` arm becomes an
  # `{:absurd}` branch; coverage is enforced by the kernel's check_coverage.
  defp elaborate_with_branches(arms, %{ctx: ctx, env: env, dname: dname} = cfg) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname),
         :ok <- reject_with_default(default) do
      arm_map
      |> Enum.reduce_while({:ok, []}, fn
        {cname, {:impossible_marked, _pattern}}, {:ok, acc} ->
          {arity, _} = ctor_arity(env, cname)
          {:cont, {:ok, acc ++ [{cname, arity, {:absurd}}]}}

        {cname, {:matched, pattern, body_expr}}, {:ok, acc} ->
          case elaborate_with_branch(cname, pattern, body_expr, cfg) do
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end
      end)
    end
  end

  # A `with`/`with`-rematch clause refines by restating constructor patterns; a
  # bare variable/wildcard catch-all has no refinement to offer here.
  defp reject_with_default(nil), do: :ok
  defp reject_with_default({vname, _body}), do: {:error, {:unsupported_pattern, {:default_in_with, vname}}}

  defp elaborate_with_branch(cname, pattern, body_expr, cfg) do
    %{
      names: names,
      ctx: ctx,
      env: env,
      param_vals: param_vals,
      motive: motive,
      need_eq: need_eq
    } = cfg

    {:ok, {^cname, pattern_vars}} = constructor_pattern(pattern)
    %{args: telescope, quantities: quantities} = Inductive.get_ctor(env, cname)
    arity = length(telescope)
    branch_names0 = branch_scope(quantities, pattern_vars) ++ names
    branch_ctx0 = extend_context(ctx, telescope, param_vals)

    ctor_term = branch_constructor_term(cname, arity)
    motive_shifted = Subst.shift(motive, arity, 0)
    applied = Kernel.normalize(branch_ctx0, {:app, motive_shifted, ctor_term})

    if need_eq do
      elaborate_with_eq_branch(cname, arity, ctor_term, applied, branch_ctx0, branch_names0, body_expr, cfg)
    else
      with {:ok, body_term} <-
             elaborate_branch_body(body_expr, applied, branch_names0, branch_ctx0, env) do
        {:ok, {cname, arity, body_term}}
      end
    end
  end

  # The Eq-arrow branch: bind `prf : Eq(T,e,pat)`, transport each `e`-mentioning
  # sibling to its refined type, check the arm body under the refined names, and
  # wrap as `λprf. (λh_1. … (λh_m. body) t_m …) t_1`.
  defp elaborate_with_eq_branch(cname, arity, ctor_term, applied, branch_ctx0, branch_names0, body_expr, cfg) do
    %{env: env, siblings: siblings, prf_name: prf_name,
      scrut_term: scrut_term, scrut_type_term: scrut_type_term} = cfg

    # `applied` = Π(prf : Eq(T,e,pat)). G[e↦pat]. Bind prf → the branch_ctx1 frame.
    {:pi, eq_dom_term, cod_b1} = applied
    eq_dom_value = Eval.eval(eq_dom_term, Context.env(branch_ctx0))
    branch_ctx1 = Context.extend(branch_ctx0, eq_dom_value)
    branch_names1 = [prf_name | branch_names0]

    # Constants in the branch_ctx1 frame (ctx + ctor telescope + prf).
    sc = arity + 1
    e_b1 = Subst.shift(scrut_term, sc, 0)
    t_b1 = Subst.shift(scrut_type_term, sc, 0)
    pat_b1 = Subst.shift(ctor_term, 1, 0)

    # Per-sibling transport (`prf = {:var,0}`; original `h_j` = {:var, idx+sc}).
    sib_data =
      Enum.map(siblings, fn %{index: idx, name: sname, type_term: h_ctx} ->
        h_b1 = Subst.shift(h_ctx, sc, 0)
        motive_j = {:lam, t_b1, abstract_term(h_b1, e_b1, 0)}
        transport = {:rewrite, {:var, 0}, motive_j, {:var, idx + sc}}
        %{name: sname, dom: replace_term(h_b1, e_b1, pat_b1), transport: transport}
      end)

    m = length(sib_data)

    branch_ctx_full =
      Enum.reduce(sib_data, branch_ctx1, fn %{dom: d}, c ->
        Context.extend(c, Eval.eval(d, Context.env(branch_ctx1)))
      end)

    body_names = Enum.reduce(sib_data, branch_names1, fn %{name: s}, acc -> [s | acc] end)
    cod_expected = Kernel.normalize(branch_ctx_full, Subst.shift(cod_b1, m, 0))

    with {:ok, inner} <-
           elaborate_branch_body(body_expr, cod_expected, body_names, branch_ctx_full, env) do
      wrapped =
        sib_data
        |> Enum.with_index()
        |> Enum.reverse()
        |> Enum.reduce(inner, fn {%{dom: d, transport: t}, i}, acc ->
          {:app, {:lam, Subst.shift(d, i, 0), acc}, Subst.shift(t, i, 0)}
        end)

      {:ok, {cname, arity, {:lam, eq_dom_term, wrapped}}}
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

    # Map each scrutinee index to the de Bruijn index of its motive binder jₖ
    # (which sits at depth k-pos above the body). A *variable* index position
    # rebinds directly by its de Bruijn name. A *computed* index position — e.g.
    # `app(p, q)`, whose result index is not a single variable — cannot be named
    # that way, so we abstract the whole index *term* out of the result type:
    # every occurrence of that computed index is replaced by a fresh sentinel
    # variable that then rebinds to the position's motive binder. This is the
    # standard casesOn/kabstract motive extended to computed result indices
    # (Lean `inductive.cpp:643-646` reads each ctor's result-index *terms* — which
    # may be arbitrary computed terms — and applies the motive to them): each
    # branch's goal refines to the constructor's own index (`F(app as bs)`,
    # `F(SNil)`), sound with no carried equation because the kernel checks every
    # branch at `motive @ ctor_indices` while the use site recovers the original
    # goal via `motive @ scrutinee_indices`. Sentinels are chosen above every free
    # de Bruijn index in play so they cannot alias a real variable or each other.
    sentinel_base = 1 + max_free_ref([result_type_term, scrut_term | idx_terms])

    {result_type_term, rebind} =
      idx_terms
      |> Enum.with_index()
      |> Enum.reduce({result_type_term, %{}}, fn
        {{:var, orig}, pos}, {rt, acc} ->
          {rt, Map.put(acc, orig, k - pos)}

        {computed, pos}, {rt, acc} ->
          sentinel = sentinel_base + pos
          {replace_term(rt, computed, {:var, sentinel}), Map.put(acc, sentinel, k - pos)}
      end)

    # The scrutinee VALUE rebinds to the motive's last binder `x`. A variable
    # scrutinee rebinds by name; a *computed* scrutinee (e.g. `view(n)`) is
    # abstracted out of the result type the same sentinel way as a computed
    # index — this is Lean's `kabstract result.matchType discr`
    # (`Elab/Match.lean:137`), which abstracts occurrences of the discriminant
    # TERM whether or not it is a variable. Without it a goal like
    # `Eq(NV(n), view(n), view(n))` keeps `view(n)` opaque per branch, and
    # `vs(toS(m)) ≢ vs(s)` — no amount of index refinement can recover it.
    {result_type_term, rebind} =
      case scrut_term do
        {:var, orig} ->
          {result_type_term, Map.put(rebind, orig, 0)}

        computed ->
          sentinel = sentinel_base + k
          {replace_term(result_type_term, computed, {:var, sentinel}),
           Map.put(rebind, sentinel, 0)}
      end

    body = generalize(result_type_term, rebind, k + 1, 0)

    (index_types ++ [scrut_type])
    |> Enum.reverse()
    |> Enum.reduce(body, fn type, acc -> {:lam, type, acc} end)
  end

  # Step 3b detection. Return `nil` unless the scrutinee has EXACTLY ONE computed
  # (non-variable) index position whose term is mentioned by at least one sibling
  # in scope (a context variable other than the scrutinee). In that case return
  # `%{pos, idx_term, idx_type_term, siblings}` describing the equation to carry.
  # Restricted to a single computed index with a closed index type (SList, Dec —
  # the FRP carriers); anything else falls back to the plain 3a motive (the kernel
  # then rejects an un-transportable sibling, never mis-accepts it).
  defp detect_carried_index(index_tele, idx_terms, scrut_term, names, ctx, env) do
    computed =
      idx_terms
      |> Enum.with_index()
      |> Enum.reject(fn {t, _pos} -> match?({:var, _}, t) end)

    with [{idx_term, pos}] <- computed,
         {_name, idx_type_term} <- Enum.at(index_tele, pos),
         true <- MapSet.size(free_indices(idx_type_term, 0)) == 0,
         [_ | _] = siblings <- collect_index_siblings(scrut_term, idx_term, names, ctx, env) do
      %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term, siblings: siblings}
    else
      _ -> nil
    end
  end

  # Siblings whose (reified) type mentions the computed index term `idx_term`,
  # EXCLUDING the scrutinee itself (its own type mentions the index but it is the
  # thing being eliminated, not transported). Innermost-first, like
  # `collect_with_siblings`. Interdependent siblings are not pre-screened here; a
  # transport that would be ill-typed is caught by the kernel's re-check.
  defp collect_index_siblings(scrut_term, idx_term, names, ctx, env) do
    depth = Context.length(ctx)
    scrut_idx = case scrut_term do
      {:var, i} -> i
      _ -> -1
    end

    names
    |> Enum.with_index()
    |> Enum.flat_map(fn {name, i} ->
      if is_binary(name) and i != scrut_idx do
        type_term = resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env)

        if contains_term?(type_term, idx_term),
          do: [%{name: name, index: i, type_term: type_term}],
          else: []
      else
        []
      end
    end)
    |> Enum.sort_by(& &1.index, :desc)
  end

  # Inject the carried index equation into a 3a motive `λj̄. λx. G'`, yielding
  # `λj̄. λx. Eq(T, idx, jₚₒₛ) -> G'`. Under the k+1 motive binders (indices j̄
  # then scrutinee x), `jₚₒₛ` sits at de Bruijn `k - pos`; `idx`/`T` are shifted
  # from the outer frame past all k+1 binders; `G'` shifts +1 past the new Eq
  # binder.
  defp wrap_motive_carried_eq(motive, k, %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term}) do
    {binder_types, body} = peel_lams(motive, k + 1, [])

    eq_dom =
      {:eq, Subst.shift(idx_type_term, k + 1, 0), Subst.shift(idx_term, k + 1, 0), {:var, k - pos}}

    new_body = {:pi, eq_dom, Subst.shift(body, 1, 0)}

    Enum.reduce(binder_types, new_body, fn type, acc -> {:lam, type, acc} end)
  end

  # Peel `n` leading `{:lam, dom, body}` binders, returning `{doms_outermost_first,
  # inner_body}`.
  defp peel_lams(body, 0, acc), do: {Enum.reverse(acc), body}
  defp peel_lams({:lam, dom, body}, n, acc), do: peel_lams(body, n - 1, [dom | acc])

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
  # `idx_vals` are the scrutinee's index VALUES (for branch_unify); each
  # branch's expected type comes from the kernel's branch_unify verdict subst
  # plus the scrutinee-value refinement (see elaborate_matched_branch).
  defp elaborate_branches(arms, names, ctx, env, dname, idx_vals, param_vals, scrut_term, result_type_term, carried) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname) do
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
                   param_vals, scrut_term, result_type_term, carried
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
            # omitted constructor — discharge if impossible, else covered by a
            # variable/wildcard catch-all (`x -> …`), else a genuine gap.
            cond do
              verdict == :impossible ->
                {arity, _} = ctor_arity(env, cname)
                {:cont, {:ok, acc ++ [{cname, arity, {:absurd}}]}}

              default != nil ->
                case elaborate_default_branch(
                       verdict, cname, default, names, ctx, env,
                       param_vals, scrut_term, result_type_term, carried
                     ) do
                  {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
                  {:error, _} = err -> {:halt, err}
                end

              true ->
                {:halt, {:error, {:missing_branch, cname}}}
            end
        end
      end)
    end
  end

  # --- as-pattern desugaring (parity #4) -------------------------------------
  #
  # `name @ <pattern>` binds the whole matched value to `name` as well as
  # destructuring it. Inline `{:as_pattern, _, [name, sub]}` nodes may sit at the
  # arm's top level OR nested inside constructor arguments (`Cons(h, t @ …)`).
  # Strip them out of the pattern tree and, since a pattern and its
  # value-reconstruction share the same surface shape, substitute each `name` by
  # its (cleaned) sub-pattern in the body — the cleaned pattern then flows through
  # nested-pattern lowering unchanged.
  defp desugar_as_patterns(arms) do
    Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, meta, body} = arm, {:ok, acc} ->
      pattern = Keyword.fetch!(meta, :pattern)
      {clean, subs} = strip_as_patterns(pattern)

      cond do
        subs == [] ->
          {:cont, {:ok, acc ++ [arm]}}

        binds_any?(single_body(body), Enum.map(subs, &elem(&1, 0))) ->
          {:halt, {:error, {:unsupported_pattern, :shadowed_as}}}

        true ->
          b2 =
            Enum.reduce(subs, single_body(body), fn {name, recon}, b ->
              subst_surface_var(b, name, recon)
            end)

          {:cont, {:ok, acc ++ [{:match_arm, Keyword.put(meta, :pattern, clean), b2}]}}
      end
    end)
  end

  # Strip inline as-patterns from a pattern tree → `{cleaned_pattern, [{name,
  # reconstruction}]}`. The reconstruction is the cleaned sub-pattern (valid as an
  # expression). Handles nesting: `w @ S(t @ Z())` yields `w ↦ S(Z())`, `t ↦ Z()`.
  defp strip_as_patterns({:as_pattern, _m, [name, sub]}) do
    {clean_sub, subs} = strip_as_patterns(sub)
    {clean_sub, [{name, clean_sub} | subs]}
  end

  defp strip_as_patterns({:function_call, m, args}) do
    {clean_args, subs} =
      Enum.map_reduce(args, [], fn a, acc ->
        {ca, s} = strip_as_patterns(a)
        {ca, acc ++ s}
      end)

    {{:function_call, m, clean_args}, subs}
  end

  defp strip_as_patterns(other), do: {other, []}

  # --- tuple sub-patterns inside a constructor argument (parity #4) -----------
  #
  # `A(%[x, y]) -> body` destructures a Σ-typed field. Replace each tuple
  # constructor-argument with a fresh `$tup_i` binder (the `$` prefix cannot clash
  # with a user identifier) and substitute the tuple's variables by projections of
  # that binder in the body — so `A(%[x, y]) -> body` becomes
  # `A($tup_0) -> body[x ↦ $tup_0.1, y ↦ $tup_0.2]`, which then flows through the
  # ordinary all-variable constructor path. Only direct constructor arguments are
  # rewritten; a top-level tuple pattern is left for `try_tuple_match`, and a tuple
  # nested inside a *nested* constructor falls through to that path's clean error.
  defp desugar_tuple_args(arms) do
    Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, meta, body} = arm, {:ok, acc} ->
      case strip_tuple_args_in_ctor(Keyword.fetch!(meta, :pattern)) do
        {:ok, _clean, []} ->
          {:cont, {:ok, acc ++ [arm]}}

        {:ok, clean, subs} ->
          b = single_body(body)

          if binds_any?(b, Enum.map(subs, &elem(&1, 0))) do
            {:halt, {:error, {:unsupported_pattern, :shadowed_tuple_arg}}}
          else
            b2 = Enum.reduce(subs, b, fn {n, r}, acc_b -> subst_surface_var(acc_b, n, r) end)
            {:cont, {:ok, acc ++ [{:match_arm, Keyword.put(meta, :pattern, clean), b2}]}}
          end

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  defp strip_tuple_args_in_ctor({:function_call, m, args}) do
    args
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], []}, fn {arg, i}, {:ok, cargs, subs} ->
      case arg do
        {:tuple, _tm, [_, _ | _] = elems} ->
          fresh_var = {:variable, [], "$tup_" <> Integer.to_string(i)}

          case tuple_subs(elems, fresh_var) do
            {:ok, s} -> {:cont, {:ok, cargs ++ [fresh_var], subs ++ s}}
            {:error, _} = err -> {:halt, err}
          end

        _ ->
          {:cont, {:ok, cargs ++ [arg], subs}}
      end
    end)
    |> case do
      {:ok, cargs, subs} -> {:ok, {:function_call, m, cargs}, subs}
      {:error, _} = err -> err
    end
  end

  defp strip_tuple_args_in_ctor(other), do: {:ok, other, []}

  # --- tuple-pattern matching (parity #4) ------------------------------------
  #
  # A Σ/pair is irrefutable — a single tuple-pattern arm `%[x, y] -> body` just
  # destructures. Lower it to the (already-supported) projections `.1`/`.2`:
  # `body[x ↦ p.1, y ↦ p.2]`, elaborated directly. Restricted to a VARIABLE
  # scrutinee (so the projections are cheap and re-evaluation-free) and a flat
  # 2-element tuple of variables/wildcards; anything else falls through to the
  # ordinary (`{:vdata}`) dispatch and its clean error.
  defp try_tuple_match({:variable, _sm, _sn} = scrut, [{:match_arm, meta, body}], expected, names, ctx, env) do
    case Keyword.fetch!(meta, :pattern) do
      {:tuple, _tm, [_, _ | _] = elems} ->
        with {:ok, subs} <- tuple_subs(elems, scrut) do
          b = single_body(body)

          if binds_any?(b, Enum.map(subs, &elem(&1, 0))) do
            {:error, {:unsupported_pattern, :shadowed_tuple}}
          else
            b2 = Enum.reduce(subs, b, fn {n, r}, acc -> subst_surface_var(acc, n, r) end)
            elaborate_expr_checked(b2, expected, names, ctx, env)
          end
        end

      _ ->
        :not_applicable
    end
  end

  defp try_tuple_match(_scrut, _arms, _expected, _names, _ctx, _env), do: :not_applicable

  # A single variable/wildcard arm ignores the scrutinee's structure — an
  # irrefutable bind valid at ANY scrutinee type (Σ, primitive, data), not just
  # `{:vdata}`. The scrutinee is already elaborated (so it is well-typed) before
  # this runs; `_` discards it and a name binds the whole value. This lets a
  # pair/primitive scrutinee carry a lone catch-all without the vdata dispatch
  # rejecting it as `:match_scrutinee_not_data`.
  defp try_trivial_match(scrut_expr, [{:match_arm, meta, body}], expected, names, ctx, env) do
    case Keyword.fetch!(meta, :pattern) do
      {:variable, _m, "_"} ->
        elaborate_expr_checked(single_body(body), expected, names, ctx, env)

      {:variable, _m, name} ->
        b = single_body(body)

        cond do
          # A complex scrutinee would be duplicated by substitution; leave those to
          # the ordinary path (which binds via the case machinery).
          not match?({:variable, _sm, _sn}, scrut_expr) -> :not_applicable
          binds_any?(b, [name]) -> {:error, {:unsupported_pattern, :shadowed_catchall}}
          true -> elaborate_expr_checked(subst_surface_var(b, name, scrut_expr), expected, names, ctx, env)
        end

      _ ->
        :not_applicable
    end
  end

  defp try_trivial_match(_scrut, _arms, _expected, _names, _ctx, _env), do: :not_applicable

  # An n-element tuple type is a right-nested Σ, so `%[e1, …, en]` projects as
  # `e1 = base.1`, `e2 = base.2.1`, …, `en = base.2.….2` (the final tail). Each
  # element may itself be a nested tuple, recursing on its own projection base.
  defp tuple_subs([last], base), do: tuple_elem_sub(last, base)

  defp tuple_subs([e | rest], base) do
    with {:ok, s1} <- tuple_elem_sub(e, tuple_proj(base, "1")),
         {:ok, s2} <- tuple_subs(rest, tuple_proj(base, "2")) do
      {:ok, s1 ++ s2}
    end
  end

  defp tuple_proj(base, n), do: {:attribute_access, [attribute: n], [base]}

  defp tuple_elem_sub({:variable, _m, "_"}, _proj), do: {:ok, []}
  defp tuple_elem_sub({:variable, _m, name}, proj), do: {:ok, [{name, proj}]}
  defp tuple_elem_sub({:tuple, _m, [_, _ | _] = sub_elems}, proj), do: tuple_subs(sub_elems, proj)
  defp tuple_elem_sub(_other, _proj), do: {:error, {:unsupported_pattern, :nested_tuple_element}}

  # --- nested-pattern desugaring (parity #3) ---------------------------------
  #
  # Lower nested constructor sub-patterns (`S(S(m))`, `MkPair(Z(), y)`) into
  # nested *single-level* matches, so the existing dependent match machinery
  # (motives, index refinement, catch-all) handles every level unchanged — the
  # kernel `:case` already nests, so this is purely a surface lowering pass. Runs
  # one level per `elaborate_match`; deeper nesting is lowered on re-entry when
  # the emitted inner match is elaborated.
  #
  # Scope: arms are grouped by their outer constructor; each group's argument
  # columns are compiled by the standard pattern-matrix algorithm
  # (Augustsson/Maranget) — left-to-right column selection producing a tree of
  # single-scrutinee matches, so ANY number of nested columns is handled. A
  # top-level catch-all (`_`/`x`) mixed with nesting is woven in as a fallback
  # row for the sub-patterns each nested group leaves uncovered, and kept as the
  # outer catch-all for wholly-unmatched constructors.
  defp desugar_nested_arms(arms, scrut_expr) do
    cond do
      not Enum.any?(arms, &arm_has_nested?/1) ->
        {:ok, arms}

      Enum.any?(arms, &default_arm?/1) ->
        desugar_with_default(arms, scrut_expr)

      true ->
        compile_nested_groups(arms)
    end
  end

  # A nested match with a trailing top-level catch-all `… | x -> d`. Resolve the
  # catch-all body (binding its name to the scrutinee), weave it as a wildcard
  # fallback row into every nested group so uncovered sub-patterns fall through to
  # it, then keep a top-level `_ -> d` for constructors with no arm at all.
  defp desugar_with_default(arms, scrut_expr) do
    {ctor_arms, defaults} = Enum.split_with(arms, &(not default_arm?(&1)))

    with [{:match_arm, dmeta, dbody0}] <- defaults,
         true <- default_arm?(List.last(arms)) or :not_last,
         {:variable, _m, dvname} <- Keyword.fetch!(dmeta, :pattern),
         {:ok, dbody} <- resolve_default_body(dvname, single_body(dbody0), scrut_expr) do
      with {:ok, compiled} <- compile_nested_groups(weave_default(ctor_arms, dbody)) do
        {:ok, compiled ++ [{:match_arm, [pattern: {:variable, [], "_"}], dbody}]}
      end
    else
      _ -> {:error, {:unsupported_pattern, :catchall_with_nesting}}
    end
  end

  # `_` needs no binding; a named catch-all binds the whole scrutinee, so it is
  # only supported over a variable scrutinee (substitute its name), never a
  # complex scrutinee expression (nothing to bind to).
  defp resolve_default_body("_", dbody, _scrut), do: {:ok, dbody}

  defp resolve_default_body(dvname, dbody, {:variable, _m, sname}) do
    if binds_any?(dbody, [dvname]),
      do: {:error, :shadowed},
      else: {:ok, subst_surface_var(dbody, dvname, {:variable, [], sname})}
  end

  defp resolve_default_body(_dvname, _dbody, _scrut), do: {:error, :nonvariable_scrutinee}

  # Append a wildcard fallback arm (`C(_…) -> d`) to each group that has nesting,
  # so the group's matrix falls back to the catch-all body for uncovered
  # sub-patterns. Non-nested groups are already exhaustive and left untouched.
  defp weave_default(ctor_arms, dbody) do
    order = ctor_arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
    grouped = Enum.group_by(ctor_arms, &arm_ctor_name/1)

    Enum.flat_map(order, fn cname ->
      group = Map.fetch!(grouped, cname)

      if Enum.any?(group, &arm_has_nested?/1) do
        {:function_call, fmeta, args0} = arm_pattern(hd(group))
        wilds = for i <- 1..length(args0)//1, do: {:variable, [], "$fb" <> cname <> Integer.to_string(i)}
        group ++ [{:match_arm, [pattern: {:function_call, fmeta, wilds}], dbody}]
      else
        group
      end
    end)
  end

  defp arm_pattern({:match_arm, meta, _body}), do: Keyword.fetch!(meta, :pattern)

  defp default_arm?({:match_arm, meta, _body}),
    do: match?({:variable, _m, _v}, Keyword.fetch!(meta, :pattern))

  defp arm_has_nested?({:match_arm, meta, _body}) do
    case Keyword.fetch!(meta, :pattern) do
      {:function_call, _m, args} -> Enum.any?(args, &(not match?({:variable, _mm, _v}, &1)))
      _ -> false
    end
  end

  # Group arms by outer constructor (first-appearance order, within-group order
  # preserved for first-match), then compile each group to one single-level arm.
  defp compile_nested_groups(arms) do
    order = arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
    grouped = Enum.group_by(arms, &arm_ctor_name/1)

    Enum.reduce_while(order, {:ok, []}, fn cname, {:ok, acc} ->
      case compile_ctor_group(cname, Map.fetch!(grouped, cname)) do
        {:ok, group_arms} -> {:cont, {:ok, acc ++ group_arms}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp arm_ctor_name({:match_arm, meta, _body}) do
    {:function_call, fmeta, _args} = Keyword.fetch!(meta, :pattern)
    Keyword.fetch!(fmeta, :name)
  end

  # A group with a nested arm is compiled by the matrix algorithm; a group with
  # none is passed through unchanged (so a genuine duplicate constructor still
  # reaches `partition_arms`' duplicate check).
  defp compile_ctor_group(_cname, arms) do
    if Enum.any?(arms, &arm_has_nested?/1), do: compile_group(arms), else: {:ok, arms}
  end

  # `arms` all share an outer constructor `C/k`. Emit `C(v₁..v_k) -> <matrix>`,
  # where `<matrix>` compiles the k argument columns (rows = each arm's sub-
  # patterns → body) into a tree of single-scrutinee matches.
  defp compile_group([{:match_arm, meta0, _} | _] = arms) do
    {:function_call, fmeta, args0} = Keyword.fetch!(meta0, :pattern)
    cname = Keyword.fetch!(fmeta, :name)
    k = length(args0)

    # Shadow guard: a naive surface substitution would capture if a body rebinds
    # one of the pattern variables it substitutes. Reject rather than miscompile.
    pvars =
      arms
      |> Enum.flat_map(fn {:match_arm, m, _} ->
        {:function_call, _fm, as} = Keyword.fetch!(m, :pattern)
        Enum.flat_map(as, &pattern_vars_deep/1)
      end)
      |> Enum.uniq()

    if Enum.any?(arms, fn {:match_arm, _m, b} -> binds_any?(single_body(b), pvars) end) do
      {:error, {:unsupported_pattern, :shadowed_nested}}
    else
      fresh = for i <- 1..k//1, do: "$n" <> cname <> Integer.to_string(i)

      rows =
        Enum.map(arms, fn {:match_arm, m, b} ->
          {:function_call, _fm, as} = Keyword.fetch!(m, :pattern)
          {as, single_body(b)}
        end)

      case compile_matrix(fresh, rows) do
        {:ok, inner} ->
          outer_pat = {:function_call, fmeta, Enum.map(fresh, &{:variable, [], &1})}
          {:ok, [{:match_arm, [pattern: outer_pat], inner}]}

        {:error, _} = err ->
          err
      end
    end
  end

  defp pattern_vars_deep({:variable, _m, v}), do: [v]
  defp pattern_vars_deep({:function_call, _m, args}), do: Enum.flat_map(args, &pattern_vars_deep/1)
  defp pattern_vars_deep(_), do: []

  # Pattern-matrix compilation. `scruts` are fresh scrutinee variable NAMES; each
  # row is `{[pattern…], body}` with one pattern per remaining scrutinee. Emits a
  # tree of single-scrutinee `{:pattern_match}` nodes; every emitted match is
  # single-level, so it re-uses the dependent elaborator per node.
  defp compile_matrix([], [{[], body} | _]), do: {:ok, body}

  defp compile_matrix([v | vs], rows) do
    col = Enum.map(rows, fn {[p | _ps], _b} -> p end)

    if Enum.all?(col, &match?({:variable, _m, _n}, &1)) do
      # All-variable column: bind each row's variable to `v`, drop the column.
      rows2 =
        Enum.map(rows, fn {[{:variable, _m, x} | ps], body} ->
          {ps, subst_surface_var(body, x, {:variable, [], v})}
        end)

      compile_matrix(vs, rows2)
    else
      compile_matrix_split(v, vs, rows, col)
    end
  end

  # Column `v` has ≥1 constructor pattern: branch on each distinct constructor
  # (first-appearance order), plus a catch-all if any row has a variable there.
  defp compile_matrix_split(v, vs, rows, col) do
    ctors =
      col
      |> Enum.flat_map(fn
        {:function_call, m, _a} -> [Keyword.fetch!(m, :name)]
        _ -> []
      end)
      |> Enum.uniq()

    has_var = Enum.any?(col, &match?({:variable, _m, _n}, &1))

    with {:ok, ctor_arms} <- split_ctor_arms(ctors, v, vs, rows) do
      arms =
        if has_var do
          {:ok, default_inner} = split_default(v, vs, rows)
          ctor_arms ++ [{:match_arm, [pattern: {:variable, [], v <> "_d"}], default_inner}]
        else
          ctor_arms
        end

      {:ok, {:pattern_match, [], [{:variable, [], v} | arms]}}
    end
  end

  defp split_ctor_arms(ctors, v, vs, rows) do
    Enum.reduce_while(ctors, {:ok, []}, fn cname, {:ok, acc} ->
      arity = split_arity(cname, rows)
      ws = for i <- 1..arity//1, do: v <> "_" <> cname <> Integer.to_string(i)

      sub_rows =
        Enum.flat_map(rows, fn {[p | ps], body} ->
          case p do
            {:function_call, m, qs} ->
              if Keyword.fetch!(m, :name) == cname, do: [{qs ++ ps, body}], else: []

            {:variable, _m, x} ->
              wilds = for w <- ws, do: {:variable, [], w <> "_x"}
              [{wilds ++ ps, subst_surface_var(body, x, {:variable, [], v})}]
          end
        end)

      case compile_matrix(ws ++ vs, sub_rows) do
        {:ok, inner} ->
          pat = {:function_call, [name: cname], Enum.map(ws, &{:variable, [], &1})}
          {:cont, {:ok, acc ++ [{:match_arm, [pattern: pat], inner}]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  # Arity of `cname` from the first row that mentions it explicitly.
  defp split_arity(cname, rows) do
    Enum.find_value(rows, 0, fn {[p | _], _} ->
      case p do
        {:function_call, m, qs} -> if Keyword.fetch!(m, :name) == cname, do: length(qs)
        _ -> nil
      end
    end)
  end

  # Catch-all sub-matrix for constructors not explicitly listed: only the
  # variable rows survive (each binding its variable to `v`), column dropped.
  defp split_default(v, vs, rows) do
    default_rows =
      Enum.flat_map(rows, fn {[p | ps], body} ->
        case p do
          {:variable, _m, x} -> [{ps, subst_surface_var(body, x, {:variable, [], v})}]
          _ -> []
        end
      end)

    compile_matrix(vs, default_rows)
  end

  # Build `{arm_map, default}` where arm_map is cname => {:matched, pattern, body}
  # | {:impossible_marked, pattern}, and `default` is `nil` or `{vname, body}` for
  # a single variable/wildcard catch-all arm (`x -> …` / `_ -> …`), which covers
  # every constructor not explicitly matched (Idris/Lean variable-pattern
  # coverage). Validates every constructor arm names one of dname's OWN declared
  # constructors (spec §5 step 2 gap) and rejects duplicate arms / duplicate
  # defaults / an impossible-marked catch-all.
  defp partition_arms(arms, ctx, env, dname) do
    sig = Context.signature(ctx)

    Enum.reduce_while(arms, {:ok, {%{}, nil}}, fn {:match_arm, arm_meta, body}, {:ok, {acc, default}} ->
      pattern = Keyword.fetch!(arm_meta, :pattern)

      case pattern do
        {:variable, _vmeta, vname} ->
          cond do
            Keyword.get(arm_meta, :impossible) == true ->
              {:halt, {:error, {:impossible_default_pattern, vname}}}

            default != nil ->
              {:halt, {:error, {:duplicate_default_pattern, vname}}}

            true ->
              {:cont, {:ok, {acc, {vname, single_body(body)}}}}
          end

        _ ->
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
                  {:cont, {:ok, {Map.put(acc, cname, {:impossible_marked, pattern}), default}}}

                true ->
                  {:cont, {:ok, {Map.put(acc, cname, {:matched, pattern, single_body(body)}), default}}}
              end
          end
      end
    end)
  end

  # A variable/wildcard catch-all covers `cname` (not explicitly matched): rebuild
  # the constructor pattern `cname(fresh…)`, substitute the catch-all's name with
  # that reconstruction in the body (so the bound var resolves to the very term
  # the kernel's branch goal expects), and route through the normal matched-branch
  # path — index inversion, goal refinement, carried-eq, and scrutinee
  # substitution all apply unchanged. E-layer, no TCB.
  defp elaborate_default_branch(verdict, cname, {vname, body_expr}, names, ctx, env, param_vals, scrut_term, result_type_term, carried) do
    # A surface constructor pattern names only the PRESENT (non-erased) args; the
    # erased indices are reconstructed from the telescope, not bound in the source.
    %{quantities: quantities} = Inductive.get_ctor(env, cname)
    present = Enum.count(quantities, &(&1 == :present))
    fresh = default_pattern_vars(cname, present)
    syn_pattern = {:function_call, [name: Atom.to_string(cname)], Enum.map(fresh, &{:variable, [], &1})}

    cond do
      vname == "_" ->
        elaborate_matched_branch(verdict, syn_pattern, body_expr, names, ctx, env, param_vals, scrut_term, result_type_term, carried)

      binds_any?(body_expr, [vname]) ->
        # The catch-all's name is rebound inside its own body; a naive surface
        # substitution would capture. Reject rather than miscompile.
        {:error, {:unsupported_pattern, :shadowed_default}}

      true ->
        body2 = subst_surface_var(body_expr, vname, syn_pattern)
        elaborate_matched_branch(verdict, syn_pattern, body2, names, ctx, env, param_vals, scrut_term, result_type_term, carried)
    end
  end

  # Fresh, collision-proof binder names for a synthesized catch-all constructor
  # pattern (`$<ctor>_<n>`); empty for a nullary constructor.
  defp default_pattern_vars(cname, arity) do
    for i <- 1..arity//1, do: "$" <> Atom.to_string(cname) <> "_" <> Integer.to_string(i)
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

  defp elaborate_matched_branch(verdict, pattern, body_expr, names, ctx, env, scrut_param_vals, scrut_term, result_type_term, carried) do
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

      _solved_or_trivial when carried != nil ->
        elaborate_carried_eq_branch(
          cname, telescope, result_indices, body_expr, branch_names,
          ctx, env, scrut_param_vals, result_type_term, carried
        )

      _solved_or_trivial ->
        arity = length(telescope)

        # The kernel's `branch_unify` verdict is the COMPLETE index inversion for
        # this branch — both `ctor-arg := scrut-index` (Vec-style) AND
        # `scrut-index-var := ctor-result` (e.g. `n := Z` for `v : NV(n)` matched
        # by `vz : NV(Z)`). The with-rematch path already uses it; the plain path
        # previously reimplemented a strictly weaker subset (`branch_index_subst`)
        # that missed the second direction, so a goal mentioning the scrutinee's
        # index in a nested position (`Eq(NV(n), …)`) never refined per branch.
        subst =
          case verdict do
            {:solved, s} -> s
            :trivial -> %{}
          end

        branch_ctx =
          ctx
          |> extend_context(telescope, scrut_param_vals)
          |> specialize_branch_context_subst(subst)

        # Merge in the scrutinee VALUE substitution (`v ↦ ctor`) so a goal that
        # mentions the scrutinee value itself (`Eq(T, v, v)`) refines to the
        # branch constructor alongside the index inversion — the shared
        # `refine_branch_goal` (Task 3.4), also used by the with-rematch path.
        branch_expected =
          refine_branch_goal(result_type_term, scrut_term, cname, arity, subst, branch_ctx)

        # Lean substitutes a variable major premise by `ctor fields` in the
        # entire subgoal — context AND everything elaborated inside it
        # (`Meta/Tactic/Cases.lean:219-227`, the `subst.insert majorFVarId
        # ctorApp`). Cure's surface analog: free occurrences of the scrutinee
        # NAME in the branch body become the branch pattern expression, whose
        # vars are already bound in branch scope and elaborate to exactly the
        # `ctor_term` the kernel's branch goal expects. Without this, a body
        # like `refl(v)` keeps `v` opaque (`v ≢ vz`) even though the goal
        # correctly refined to `Eq(NV(Z), vz, vz)`.
        body_expr = refine_scrutinee_in_body(body_expr, scrut_term, pattern, pattern_vars, names)

        with {:ok, body_term} <- elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
          {:ok, {cname, arity, body_term}}
        end
    end
  end

  # Step 3b branch. The motive (see `wrap_motive_carried_eq`) makes this branch's
  # expected type `Π(prf : Eq(T, idx, ctor_idx)). G'[jₚₒₛ↦ctor_idx]`, where
  # `ctor_idx` is this constructor's result index at the carried position. Bind
  # `prf`, transport each index-mentioning sibling `h : H[idx]` to `H[ctor_idx]`
  # via `rewrite prf (λz. H[idx↦z]) h`, and emit `λprf. (λh'. body) transport`.
  # Mirrors capability-B's `elaborate_with_eq_branch`, keyed on the index term.
  defp elaborate_carried_eq_branch(cname, telescope, result_indices, body_expr, branch_names, ctx, env, scrut_param_vals, result_type_term, carried) do
    %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term, siblings: siblings} = carried
    arity = length(telescope)
    branch_ctx0 = extend_context(ctx, telescope, scrut_param_vals)

    # `ctor_idx` — this constructor's result index at the carried position, in the
    # branch_ctx0 frame (telescope bound). `Eq(T, idx, ctor_idx)` is the proof the
    # motive hands each branch (kernel checks the branch at `motive @ ctor_idx`).
    ctor_idx = Enum.at(result_indices, pos)
    eq_dom_term = {:eq, Subst.shift(idx_type_term, arity, 0), Subst.shift(idx_term, arity, 0), ctor_idx}
    branch_ctx1 = Context.extend(branch_ctx0, Eval.eval(eq_dom_term, Context.env(branch_ctx0)))

    # Constants in branch_ctx1 (ctx + telescope + prf). `sc` shifts a ctx-frame
    # term past the telescope and the prf binder; `pat_b1` is `ctor_idx` past prf.
    sc = arity + 1
    idx_b1 = Subst.shift(idx_term, sc, 0)
    t_b1 = Subst.shift(idx_type_term, sc, 0)
    pat_b1 = Subst.shift(ctor_idx, 1, 0)

    sib_data =
      Enum.map(siblings, fn %{index: idx, name: sname, type_term: h_ctx} ->
        h_b1 = Subst.shift(h_ctx, sc, 0)
        motive_j = {:lam, t_b1, abstract_term(h_b1, idx_b1, 0)}
        transport = {:rewrite, {:var, 0}, motive_j, {:var, idx + sc}}
        %{name: sname, dom: replace_term(h_b1, idx_b1, pat_b1), transport: transport}
      end)

    m = length(sib_data)

    branch_ctx_full =
      Enum.reduce(sib_data, branch_ctx1, fn %{dom: d}, c ->
        Context.extend(c, Eval.eval(d, Context.env(c)))
      end)

    body_names = Enum.reduce(sib_data, [carried_prf_name() | branch_names], fn %{name: s}, acc -> [s | acc] end)

    # Refined goal for this branch (`result_type[idx ↦ ctor_idx]`) in the full
    # frame (ctx + telescope + prf + siblings), for checking-mode body forms.
    over = sc + m
    cod_expected =
      Subst.shift(result_type_term, over, 0)
      |> replace_term(Subst.shift(idx_term, over, 0), Subst.shift(ctor_idx, 1 + m, 0))
      |> then(&Kernel.normalize(branch_ctx_full, &1))

    with {:ok, inner} <- elaborate_branch_body(body_expr, cod_expected, body_names, branch_ctx_full, env) do
      wrapped =
        sib_data
        |> Enum.with_index()
        |> Enum.reverse()
        |> Enum.reduce(inner, fn {%{dom: d, transport: t}, i}, acc ->
          {:app, {:lam, Subst.shift(d, i, 0), acc}, Subst.shift(t, i, 0)}
        end)

      {:ok, {cname, arity, {:lam, eq_dom_term, wrapped}}}
    end
  end

  defp carried_prf_name, do: "$carried_idx_prf"

  defp elaborate_branch_body({:rewrite_expr, _meta, _children} = expr, expected, names, ctx, env),
    do: elaborate_expr_checked(expr, expected, names, ctx, env)

  # A nested `match` arm body is a checking-mode expression: `expected` is the
  # (index-refined) result type for this branch, exactly what its motive needs.
  defp elaborate_branch_body({:pattern_match, _meta, _children} = expr, expected, names, ctx, env),
    do: elaborate_expr_checked(expr, expected, names, ctx, env)

  defp elaborate_branch_body({:function_call, meta, _args} = expr, expected, names, ctx, env) do
    name = Keyword.get(meta, :name)

    cond do
      name == "refl" ->
        elaborate_expr_checked(expr, expected, names, ctx, env)

      is_binary(name) and Inductive.get_ctor(env, String.to_atom(name)) != nil ->
        # A constructor branch body. Infer FIRST — this preserves every case that
        # already worked, including a reconstruction whose indices the present
        # arguments determine and the carried-index-Eq transport (which wraps an
        # inferred body). ONLY when inference cannot pin the erased indices —
        # `prim()`/`seq(l,r)` reconstructed at a refined index with no present
        # argument to solve `av`/`bv` from (`:unsolved_metavariables`) — retry in
        # checking mode, letting the branch's expected type pin them.
        case elaborate_expr_typed(expr, names, ctx, env) do
          {:ok, term, _type} -> {:ok, term}
          {:error, {:unsolved_metavariables, _}} -> elaborate_expr_checked(expr, expected, names, ctx, env)
          {:error, _} = err -> err
        end

      true ->
        with {:ok, term, _type} <- elaborate_expr_typed(expr, names, ctx, env), do: {:ok, term}
    end
  end

  # A pair `%[a, b]` (dependent-pair introduction) as a branch body: a
  # checking-mode expression against this branch's (index-refined) Σ type — the
  # expected type pins the components' erased indices (an FRP `step`'s `prim()`
  # continuation has no other way to solve its index metas). Without this a
  # Σ-returning eliminator fails its arms with `:unsupported_expression`.
  defp elaborate_branch_body({:tuple, _meta, [_a, _b]} = expr, expected, names, ctx, env),
    do: elaborate_expr_checked(expr, expected, names, ctx, env)

  defp elaborate_branch_body(expr, _expected, names, ctx, env) do
    with {:ok, term, _type} <- elaborate_expr_typed(expr, names, ctx, env), do: {:ok, term}
  end

  # A `let x = e ⏎ …` block. Each `let` desugars by SURFACE substitution —
  # `let x = e in body` ≡ `body[x := e]` — then the remainder is elaborated
  # normally. This sidesteps de Bruijn bookkeeping entirely (the rhs is
  # re-elaborated at each use site of `x`; a naming convenience, not sharing).
  # Sound: a later binder that shadows `x` (or would capture a free variable of
  # `e`) is guarded by `binds_any?`; and every substituted body is re-checked by
  # the kernel, so an unsound inline yields a REJECTION, never a bad accept.
  defp elaborate_let_block([final], expected_core, names, ctx, env),
    do: elaborate_expr_checked(final, expected_core, names, ctx, env)

  defp elaborate_let_block(
         [{:assignment, meta, [{:variable, _, name}, rhs]} | rest],
         expected_core,
         names,
         ctx,
         env
       ) do
    cond do
      not Keyword.get(meta, :let, false) ->
        {:error, {:unsupported_block_statement, meta}}

      Enum.any?(rest, &binds_any?(&1, [name])) ->
        # A later statement rebinds `name` (shadowing) — surface substitution
        # would capture it; refuse rather than silently mis-inline.
        {:error, {:let_shadowed_binder, name}}

      true ->
        rest
        |> Enum.map(&subst_surface_var(&1, name, rhs))
        |> elaborate_let_block(expected_core, names, ctx, env)
    end
  end

  defp elaborate_let_block(other, _expected_core, _names, _ctx, _env),
    do: {:error, {:unsupported_block, other}}

  # Surface-level scrutinee refinement (Lean `Cases.lean:219-227`): in a branch,
  # a VARIABLE scrutinee *is* the pattern, so free occurrences of its name in
  # the branch body are replaced by the pattern expression. Bails out — leaving
  # today's behavior, which the kernel re-check keeps sound — when the name does
  # not uniquely resolve to the scrutinee (an inner binding shadows it), when
  # the pattern itself rebinds the name, or when a nested match arm binds a name
  # that would shadow the scrutinee or capture a pattern var.
  defp refine_scrutinee_in_body(body_expr, {:var, i}, pattern, pattern_vars, names) do
    scrut_name = Enum.at(names, i)

    if is_binary(scrut_name) and
         Enum.find_index(names, &(&1 == scrut_name)) == i and
         scrut_name not in pattern_vars and
         not binds_any?(body_expr, [scrut_name | pattern_vars]) do
      subst_surface_var(body_expr, scrut_name, pattern)
    else
      body_expr
    end
  end

  defp refine_scrutinee_in_body(body_expr, _scrut_term, _pattern, _pattern_vars, _names),
    do: body_expr

  defp subst_surface_var({:variable, _meta, name}, name, replacement), do: replacement

  defp subst_surface_var({tag, meta, children}, name, replacement) when is_list(children),
    do: {tag, meta, Enum.map(children, &subst_surface_var(&1, name, replacement))}

  defp subst_surface_var(other, _name, _replacement), do: other

  # Does any nested match arm bind one of `avoid`? (Arm patterns live in the
  # arm's meta, not its children, so the generic subst walk never rewrites a
  # binder position — this predicate only guards shadowing/capture in bodies.)
  defp binds_any?({:match_arm, meta, body}, avoid) do
    vars =
      case Keyword.get(meta, :pattern) do
        {:function_call, _pmeta, args} -> for {:variable, _vmeta, v} <- args, do: v
        _ -> []
      end

    Enum.any?(vars, &(&1 in avoid)) or binds_any?(body, avoid)
  end

  defp binds_any?({_tag, _meta, children}, avoid) when is_list(children),
    do: Enum.any?(children, &binds_any?(&1, avoid))

  defp binds_any?(list, avoid) when is_list(list),
    do: Enum.any?(list, &binds_any?(&1, avoid))

  defp binds_any?(_other, _avoid), do: false

  defp constructor_pattern({:function_call, meta, args}) do
    cname = meta |> Keyword.fetch!(:name) |> String.to_atom()

    # A surface constructor pattern binds only variables in its argument
    # positions. A NESTED constructor/literal sub-pattern (`S(S(m))`, `C(Z(),y)`)
    # needs decision-tree lowering (parity #3), not yet implemented — report a
    # clean error rather than crashing on the non-variable arg.
    if Enum.all?(args, &match?({:variable, _m, _v}, &1)) do
      vars = Enum.map(args, fn {:variable, _meta, v} -> v end)
      {:ok, {cname, vars}}
    else
      {:error, {:unsupported_pattern, :nested_constructor_arg}}
    end
  end

  defp constructor_pattern(other), do: {:error, {:unsupported_pattern, pattern_shape(other)}}

  defp pattern_shape(p) when is_tuple(p) and tuple_size(p) > 0, do: elem(p, 0)
  defp pattern_shape(_), do: :unknown

  @doc """
  LHS re-match (ports Idris `TTImp.WithClause.getMatch`). Match the parent
  function's original parameter patterns positionally against a with-clause's
  RESTATED patterns, producing a substitution `%{parent_var_name => refined
  surface pattern}`. This is the map that refines the branch goal and sibling
  types by the index a with-clause restates (`n` ↦ `S(m)`).

  Handled (the faithful first slice):
    * variable ↦ variable    — an alias (`n` restated as `m`)
    * variable ↦ constructor — the refinement (`n` restated as `S(m)`)
    * constructor ↦ constructor — structural recursion into matching args

  A restated pattern that is a non-constructor EXPRESSION (e.g. `k + k`) is
  rejected with `{:with_rematch_non_constructor_pattern, …}` — that is the
  deferred forced/dot-pattern case (ledger #5), not a crash.
  """
  @spec match_parent_lhs([term()], [term()]) :: {:ok, %{String.t() => term()}} | {:error, term()}
  def match_parent_lhs(originals, restated) when length(originals) == length(restated) do
    originals
    |> Enum.zip(restated)
    |> Enum.reduce_while({:ok, %{}}, fn {orig, pat}, {:ok, acc} ->
      case match_one_lhs(orig, pat, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  def match_parent_lhs(originals, restated),
    do: {:error, {:with_rematch_arity_mismatch, length(originals), length(restated)}}

  # A parent variable (or `{:param,…}`) binds to its restated pattern, provided
  # the pattern is a variable or a (possibly nested) constructor application.
  defp match_one_lhs({:variable, _, name}, restated, acc), do: bind_var_lhs(name, restated, acc)
  defp match_one_lhs({:param, _, name}, restated, acc), do: bind_var_lhs(name, restated, acc)

  # Parent constructor vs restated constructor: names + arity must agree, then
  # recurse into the arguments (the getMatch IApp case).
  defp match_one_lhs({:function_call, m1, a1}, {:function_call, m2, a2}, acc) do
    n1 = Keyword.get(m1, :name)
    n2 = Keyword.get(m2, :name)

    cond do
      n1 != n2 ->
        {:error, {:with_rematch_ctor_mismatch, n1, n2}}

      length(a1) != length(a2) ->
        {:error, {:with_rematch_arity_mismatch, length(a1), length(a2)}}

      true ->
        a1
        |> Enum.zip(a2)
        |> Enum.reduce_while({:ok, acc}, fn {o, p}, {:ok, a} ->
          case match_one_lhs(o, p, a) do
            {:ok, a2} -> {:cont, {:ok, a2}}
            {:error, _} = err -> {:halt, err}
          end
        end)
    end
  end

  defp match_one_lhs(orig, _restated, _acc),
    do: {:error, {:with_rematch_unsupported_parent_pattern, pattern_shape(orig)}}

  defp bind_var_lhs(name, restated, acc) do
    if valid_restated_pattern?(restated) do
      merge_lhs_match(acc, name, restated)
    else
      {:error, {:with_rematch_non_constructor_pattern, pattern_shape(restated)}}
    end
  end

  # mergeMatches: a name may be restated more than once only if consistently.
  defp merge_lhs_match(acc, name, pat) do
    case Map.fetch(acc, name) do
      :error -> {:ok, Map.put(acc, name, pat)}
      {:ok, existing} ->
        if strip_pattern_meta(existing) == strip_pattern_meta(pat),
          do: {:ok, acc},
          else: {:error, {:with_rematch_inconsistent_binding, name}}
    end
  end

  # A restated pattern must be a variable or a constructor application whose
  # every argument is itself such a pattern. Anything else (binary ops, literal
  # arithmetic, …) is a non-constructor expression — the deferred forced case.
  defp valid_restated_pattern?({:variable, _, _}), do: true

  defp valid_restated_pattern?({:function_call, meta, args}) do
    constructor_name?(Keyword.get(meta, :name)) and Enum.all?(args, &valid_restated_pattern?/1)
  end

  defp valid_restated_pattern?(_), do: false

  # Cure constructors are capitalised; ordinary identifiers/operators are not.
  defp constructor_name?(name) when is_binary(name) and name != "",
    do: String.first(name) =~ ~r/[A-Z]/

  defp constructor_name?(_), do: false

  # Structural equality of surface patterns, ignoring meta.
  defp strip_pattern_meta({:variable, _, n}), do: {:variable, n}

  defp strip_pattern_meta({:function_call, meta, args}),
    do: {:function_call, Keyword.get(meta, :name), Enum.map(args, &strip_pattern_meta/1)}

  defp strip_pattern_meta(other), do: other

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

  # Shared branch-goal refinement (Task 3.4) — ONE equation-compiler refinement
  # behind two front-ends (plain `match` `elaborate_matched_branch` and
  # `with`-rematch `elaborate_rematch_branch`). Composes (1a) index inversion (the
  # `branch_unify` verdict `subst`) with (1b) scrutinee-VALUE refinement: a
  # variable scrutinee is keyed into the subst at `i + arity`; a computed one has
  # its occurrences replaced by the branch constructor as a whole term (matching
  # `build_motive`'s kabstract — the kernel checks this branch at `motive @ ctor`).
  defp refine_branch_goal(result_type_term, scrut_term, cname, arity, subst, branch_ctx) do
    ctor_term = branch_constructor_term(cname, arity)

    subst_with_scrut =
      case scrut_term do
        {:var, i} -> Map.put(subst, i + arity, ctor_term)
        _other -> subst
      end

    shifted_goal = Subst.shift(result_type_term, arity, 0)

    shifted_goal =
      case scrut_term do
        {:var, _} -> shifted_goal
        computed -> replace_term(shifted_goal, Subst.shift(computed, arity, 0), ctor_term)
      end

    shifted_goal
    |> replace_branch_vars(subst_with_scrut)
    |> then(&Kernel.normalize(branch_ctx, &1))
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
  @spec elaborate_ctor_app(Env.t(), atom(), [{term(), term()}], Context.t() | nil) ::
          {:ok, term(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate_ctor_app(env, cname, present_args, ctx \\ nil, expected_core \\ nil) do
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
      pc = length(param_tele)
      init = {:ok, MetaCtx.new(), [], present_args}

      telescope
      |> Enum.reduce_while(init, &solve_arg(&1, &2, env))
      |> pin_ctor_result(expected_core, family, ctor, pc, env)
      |> finish_ctor_app(cname, family, ctor, pc, ctx)
    end
  end

  # Checking-mode index inference: unify the constructor's RESULT type (built with
  # the erased-index metavariables still open) against the expected type, pinning
  # indices the present arguments could not. A nullary constructor whose indices
  # are all erased — `prim : SF(av, bv, DCau)` reconstructed in a dependent-match
  # branch expecting `SF(as, bs, DCau)` — has NO present argument to solve `av`/`bv`
  # from; the expected type is their only source. In inference mode (`expected_core
  # == nil`) this is a no-op, so ordinary constructor applications are unchanged.
  defp pin_ctor_result({:ok, mctx, chosen, []} = ok, expected_core, family, ctor, pc, env)
       when expected_core != nil do
    {param_vals, args} = Enum.split(chosen, pc)
    seed = param_vals ++ args
    params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
    indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))
    result_term = {:data, family, params, indices}

    case Unify.unify(result_term, expected_core, mctx, env) do
      {:ok, mctx2} -> {:ok, mctx2, chosen, []}
      # Leave the mismatch to `finish_ctor_app` (unsolved metas) or the kernel's
      # own re-check — never silently accept.
      {:error, _} -> ok
    end
  end

  defp pin_ctor_result(acc, _expected_core, _family, _ctor, _pc, _env), do: acc

  # One telescope slot: erased → fresh meta; present → unify expected vs actual.
  # `env` is threaded as the conversion signature so a present argument whose type
  # carries a *computed* index (`seq`'s `dmeet(d1, d2)`) unifies up-to-δ against
  # the expected `DDec` — closing the composed-computed-index reach (Idris parity)
  # without any kernel change (`Unify` uses the trusted `Conv`; the kernel still
  # re-checks the assembled ctor). See `Unify.unify/4`.
  defp solve_arg({{_name, _type_term}, :erased}, {:ok, mctx, chosen, present}, _env) do
    {mctx, id} = MetaCtx.fresh(mctx)
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], present}}
  end

  defp solve_arg({{_name, _type_term}, :present}, {:ok, _mctx, _chosen, []}, _env),
    do: {:halt, {:error, :too_few_arguments}}

  defp solve_arg(
         {{_name, type_term}, :present},
         {:ok, mctx, chosen, [{arg, arg_type_term} | rest]},
         env
       ) do
    expected = Subst.instantiate(type_term, chosen)

    case Unify.unify(expected, arg_type_term, mctx, env) do
      {:ok, mctx} -> {:cont, {:ok, mctx, chosen ++ [arg], rest}}
      {:error, reason} -> {:halt, {:error, {:index_mismatch, reason}}}
    end
  end

  defp finish_ctor_app({:error, _} = err, _cname, _family, _ctor, _pc, _ctx), do: err

  defp finish_ctor_app({:ok, _mctx, _chosen, [_ | _]}, _cname, _family, _ctor, _pc, _ctx),
    do: {:error, :too_many_arguments}

  defp finish_ctor_app({:ok, mctx, chosen, []}, cname, family, ctor, pc, ctx) do
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

      # The result type's computed indices reference the CALLER's context vars
      # (e.g. `seq`'s result `SF(app(av,cv), …)`). Evaluate under the caller's
      # environment so those free de Bruijn variables get the correct neutral
      # levels — evaluating under `[]` mis-levels them, which is invisible when a
      # ctor is checked directly (the kernel re-infers) but CORRUPTS meta-solving
      # when this inferred type feeds further elaboration (a computed-index ctor
      # applied as another ctor's argument, e.g. `loop(seq(a,b))`). Mirrors
      # `finish_global_app`. With no caller context (isolated unit calls), fall
      # back to `[]` — those terms are closed, so the frame is immaterial.
      caller_env = if ctx, do: Context.env(ctx), else: []
      result_type = Eval.eval({:data, family, params, indices}, caller_env)
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
    |> Enum.reduce_while(init, &solve_arg(&1, &2, env))
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

  def elaborate_expr({:function_call, meta, args}, scope, env)
      when is_list(meta) do
    if Keyword.get(meta, :record) do
      with {:ok, positional} <- desugar_record_construction(meta, args, env) do
        elaborate_expr(positional, scope, env)
      end
    else
      elaborate_named_call_scoped(meta, args, scope, env)
    end
  end

  defp elaborate_named_call_scoped(meta, args, scope, env) do
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

  # Pair introduction `%[a, b]` in the scope-based term builder (function
  # arguments and other sub-terms). Emits the Core `{:pair, …}`; its Σ type is
  # derived by `Kernel.infer` on the enclosing application, which checks the pair
  # against the callee's domain (so a dependent Σ parameter is honoured too).
  def elaborate_expr({:tuple, _meta, [a, b]}, scope, env) do
    with {:ok, a_core} <- elaborate_expr(a, scope, env),
         {:ok, b_core} <- elaborate_expr(b, scope, env) do
      {:ok, {:pair, a_core, b_core}}
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
