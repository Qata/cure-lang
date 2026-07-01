defmodule Cure.Core.Kernel do
  @moduledoc """
  The trusted bidirectional type checker (design spec §4.3, §5).

  `infer/2` synthesises a type **value** for a term; `check/3` verifies a term
  against an expected type value, falling back to `infer` plus a cumulative
  conversion test on the result. Types are compared as values via
  `Cure.Core.Conv` (NbE definitional equality); universe cumulativity is applied
  at the sort level (`Type i <: Type i+1`).

  This module is part of the trusted kernel: it is small, pure, and deterministic,
  and it never trusts an elaborator-supplied type — it re-derives everything.

  Coverage grows by milestone: Type/var/Π here (M2.2), λ/application (M2.3),
  constructors (M3.4), `case` (M4), Σ (M5), `Eq`/`refl`/`rewrite` (M6), global
  definitions + certificates (M7).
  """

  alias Cure.Core.{Certificate, Context, Conv, Env, Eval, Inductive, Quote, Term, Universe}

  @type result :: {:ok, Cure.Core.Value.t()} | {:error, term()}

  @doc "Synthesise the type value of `term` in `ctx`."
  @spec infer(Context.t(), Cure.Core.Term.t()) :: result()
  def infer(_ctx, {:type, level}) do
    case Universe.succ(level) do
      {:ok, l1} -> {:ok, {:vtype, l1}}
      {:error, reason} -> {:error, reason}
    end
  end

  def infer(ctx, {:var, k}) do
    case Context.lookup(ctx, k) do
      nil -> {:error, {:unbound_var, k}}
      type_value -> {:ok, type_value}
    end
  end

  # Primitive Int/Bool/Float: base types live in `Type0`, literals inhabit them,
  # and each primitive op is typed against the kernel (arithmetic/comparison are
  # numeric-polymorphic over Int or Float; connectives are on Bool).
  def infer(_ctx, {:int_type}), do: {:ok, {:vtype, 0}}
  def infer(_ctx, {:int_lit, _n}), do: {:ok, {:vint_type}}
  def infer(_ctx, {:bool_type}), do: {:ok, {:vtype, 0}}
  def infer(_ctx, {:bool_lit, _b}), do: {:ok, {:vbool_type}}
  def infer(_ctx, {:float_type}), do: {:ok, {:vtype, 0}}
  def infer(_ctx, {:float_lit, _f}), do: {:ok, {:vfloat_type}}

  def infer(ctx, {:prim, op, args}), do: infer_prim(ctx, op, args)

  def infer(ctx, {:pi, dom, cod}) do
    with {:ok, l1} <- infer_sort(ctx, dom),
         dom_value = Eval.eval(dom, Context.env(ctx)),
         ctx2 = Context.extend(ctx, dom_value),
         {:ok, l2} <- infer_sort(ctx2, cod) do
      {:ok, {:vtype, Universe.max(l1, l2)}}
    end
  end

  def infer(ctx, {:lam, dom, body}) do
    with {:ok, _level} <- infer_sort(ctx, dom) do
      dom_value = Eval.eval(dom, Context.env(ctx))
      ctx2 = Context.extend(ctx, dom_value)

      with {:ok, cod_value} <- infer(ctx2, body) do
        # Reify the body's type into a codomain family over the binder.
        cod_term = Quote.reify(cod_value, Context.length(ctx2))
        {:ok, {:vpi, dom_value, {:closure, Context.env(ctx), cod_term}}}
      end
    end
  end

  def infer(ctx, {:global, name}) do
    case Env.get_def(Context.signature(ctx), name) do
      nil -> {:error, :unknown_global}
      %{type: type_term} -> {:ok, Eval.eval(type_term, [])}
    end
  end

  def infer(ctx, {:eq, ty, a, b}) do
    with {:ok, level} <- infer_sort(ctx, ty),
         ty_value = Eval.eval(ty, Context.env(ctx)),
         :ok <- check(ctx, a, ty_value),
         :ok <- check(ctx, b, ty_value) do
      {:ok, {:vtype, level}}
    end
  end

  def infer(ctx, {:refl, a}) do
    with {:ok, ty_value} <- infer(ctx, a) do
      a_value = Eval.eval(a, Context.env(ctx))
      {:ok, {:veq, ty_value, a_value, a_value}}
    end
  end

  def infer(ctx, {:rewrite, proof, motive, body}) do
    with {:ok, proof_type} <- infer(ctx, proof),
         {:ok, a_value, b_value} <- ensure_eq(proof_type) do
      # motive (x.M): result transports M[a/x] (the body's type) to M[b/x].
      motive_value = Eval.eval(motive, Context.env(ctx))
      expected_body = Eval.apply(motive_value, a_value)

      case check(ctx, body, expected_body) do
        :ok -> {:ok, Eval.apply(motive_value, b_value)}
        {:error, _} -> {:error, :rewrite_premise}
      end
    end
  end

  def infer(ctx, {:sigma, a, b}) do
    with {:ok, l1} <- infer_sort(ctx, a),
         a_value = Eval.eval(a, Context.env(ctx)),
         ctx2 = Context.extend(ctx, a_value),
         {:ok, l2} <- infer_sort(ctx2, b) do
      {:ok, {:vtype, Universe.max(l1, l2)}}
    end
  end

  def infer(ctx, {:fst, p}) do
    with {:ok, ptype} <- infer(ctx, p),
         {:ok, dom, _cod} <- ensure_sigma(ptype) do
      {:ok, dom}
    end
  end

  def infer(ctx, {:snd, p}) do
    with {:ok, ptype} <- infer(ctx, p),
         {:ok, _dom, cod_closure} <- ensure_sigma(ptype) do
      # Second component's type is B[fst p / x] (§4.7).
      fst_value = Eval.eval({:fst, p}, Context.env(ctx))
      {:ok, Eval.apply_closure(cod_closure, fst_value)}
    end
  end

  def infer(ctx, {:app, f, a}) do
    with {:ok, f_type} <- infer(ctx, f),
         {:ok, dom, cod_closure} <- ensure_pi(f_type),
         :ok <- check(ctx, a, dom) do
      a_value = Eval.eval(a, Context.env(ctx))
      {:ok, Eval.apply_closure(cod_closure, a_value)}
    end
  end

  def infer(ctx, {:data, name, params, indices}) do
    case Inductive.get_family(Context.signature(ctx), name) do
      nil ->
        {:error, {:unknown_family, name}}

      %{params: ptele, indices: itele, level: level} ->
        with {:ok, pvals} <- check_spine(ctx, params, ptele, []),
             {:ok, _ivals} <- check_spine(ctx, indices, itele, pvals) do
          {:ok, {:vtype, level}}
        end
    end
  end

  def infer(ctx, {:ctor, name, args}) do
    sig = Context.signature(ctx)

    case Inductive.get_ctor(sig, name) do
      nil ->
        {:error, {:unknown_ctor, name}}

      %{args: tele, result_indices: result_indices} ->
        family_name = Inductive.ctor_family(sig, name)

        with {:ok, arg_env} <- check_ctor_app(ctx, args, tele) do
          # The accumulated arg values (most-recent first) are exactly the env in
          # which the result-index terms are written; compute them by NbE (so a
          # computed index like `and(d1,d2)` reduces once δ is available, M7).
          # Slice-1 families are parameter-free; prepend evaluated params here
          # when parameters are introduced.
          index_values = Enum.map(result_indices, &Eval.eval(&1, arg_env))
          {:ok, {:vdata, family_name, index_values}}
        end
    end
  end

  def infer(ctx, {:case, scrut, motive, branches}) do
    sig = Context.signature(ctx)

    case infer(ctx, scrut) do
      {:ok, {:vdata, dname, scrut_indices}} ->
        family = Inductive.get_family(sig, dname)
        motive_value = Eval.eval(motive, Context.env(ctx))

        with :ok <- check_motive_wf(ctx, motive_value, family),
             :ok <- check_coverage(sig, dname, branches),
             :ok <- check_case_branches(ctx, sig, motive_value, branches, scrut_indices) do
          # Result type = motive at the scrutinee's actual indices and value (§4.4).
          scrut_value = Eval.eval(scrut, Context.env(ctx))
          {:ok, apply_motive(motive_value, scrut_indices ++ [scrut_value])}
        end

      {:ok, _other} ->
        {:error, :case_scrutinee_not_data}

      {:error, _} = err ->
        err
    end
  end

  @doc "Check `term` against the expected type value in `ctx`."
  @spec check(Context.t(), Cure.Core.Term.t(), Cure.Core.Value.t()) :: :ok | {:error, term()}
  # Bidirectional rule: a lambda is checked against a Π, propagating the expected
  # domain into the body (more robust than infer when the body is not standalone).
  def check(ctx, {:lam, dom, body}, {:vpi, exp_dom, cod_closure}) do
    dom_value = Eval.eval(dom, Context.env(ctx))

    if Conv.conv_values?(dom_value, exp_dom, Context.length(ctx), Context.signature(ctx)) do
      fresh = {:vneutral, {:nvar, Context.length(ctx)}}
      cod_value = Eval.apply_closure(cod_closure, fresh)
      check(Context.extend(ctx, exp_dom), body, cod_value)
    else
      {:error, :domain_mismatch}
    end
  end

  # The §4.6 soundness gate: `refl a` checks against `Eq ty a' b'` iff the
  # endpoints are definitionally equal AND `a` is convertible to them. This is
  # the fix for the audit's bug (the old checker accepted any atom as a proof).
  def check(ctx, {:refl, a}, {:veq, ty_value, a_value, b_value}) do
    with :ok <- check(ctx, a, ty_value) do
      depth = Context.length(ctx)
      a_refl = Eval.eval(a, Context.env(ctx))

      sig = Context.signature(ctx)

      if Conv.conv_values?(a_value, b_value, depth, sig) and
           Conv.conv_values?(a_refl, a_value, depth, sig) do
        :ok
      else
        {:error, :not_definitionally_equal}
      end
    end
  end

  # A dependent pair is checked against a Σ: first component against the domain,
  # second against the domain-instantiated codomain B[a/x] (§4.7).
  def check(ctx, {:pair, a, b}, {:vsigma, dom, cod_closure}) do
    with :ok <- check(ctx, a, dom) do
      a_value = Eval.eval(a, Context.env(ctx))
      expected_b = Eval.apply_closure(cod_closure, a_value)

      case check(ctx, b, expected_b) do
        :ok -> :ok
        {:error, _} -> {:error, :sigma_mismatch}
      end
    end
  end

  # A hole is a deferred term: accepted at any goal type. Its obligation is
  # reported to the user and blocks codegen until filled (§6 / M8.5).
  def check(_ctx, {:hole, _name}, _expected), do: :ok

  def check(ctx, term, expected) do
    with {:ok, inferred} <- infer(ctx, term) do
      if subtype?(inferred, expected, ctx) do
        :ok
      else
        # Conversion failure diagnostic (§10): report both normal forms so the
        # mismatch is legible (and serializable via C2 for independent checkers).
        depth = Context.length(ctx)
        {:error, {:conversion_failure, Quote.reify(inferred, depth), Quote.reify(expected, depth)}}
      end
    end
  end

  @doc """
  Type-check a registered global definition: its declared type is a valid type,
  and its body checks against that type. The kernel re-derives everything — it
  never trusts an elaborator-supplied type. (δ-unfolding stays disabled until the
  def is also totality-certified, M7.2.)
  """
  @spec check_def(Env.t(), atom()) :: :ok | {:error, term()}
  def check_def(env, name) do
    case Env.get_def(env, name) do
      nil ->
        {:error, :unknown_global}

      %{type: type_term, body: body_term} ->
        ctx = Context.empty(env)

        with {:ok, _level} <- infer_sort(ctx, type_term) do
          check(ctx, body_term, Eval.eval(type_term, []))
        end
    end
  end

  @doc """
  Re-run the totality decision procedure on a registered, type-checked global
  and, if it passes, certify it for δ-reduction (design spec §7). Coverage is
  re-checked by `check_def` (the kernel's `case` typing); termination by
  `Cure.Core.Certificate`. The kernel never trusts an elaborator's verdict — it
  re-derives certification itself, returning the signature with the global
  marked certified (the only way the certified set is populated).
  """
  @spec validate_certificate(Env.t(), atom()) :: {:ok, Env.t()} | {:error, term()}
  def validate_certificate(env, name) do
    with :ok <- check_def(env, name) do
      %{body: body} = Env.get_def(env, name)

      if Certificate.terminating?(name, body, env),
        do: {:ok, Env.certify(env, name)},
        else: {:error, :not_total}
    end
  end

  @doc """
  Check an indexed family declaration well-formed: parameter telescope, then
  index telescope (in the context of the parameters), each entry a valid type.
  """
  @spec check_family(Cure.Core.Env.t(), Inductive.family()) :: :ok | {:error, term()}
  def check_family(env, %{params: params, indices: indices}) do
    base = Context.empty(env)

    with {:ok, ctx_params} <- check_telescope(base, params),
         {:ok, _ctx} <- check_telescope(ctx_params, indices) do
      :ok
    end
  end

  @doc """
  Check a constructor well-formed against its family (§4.4): argument telescope
  well-typed; the family's declared level dominates every field type's level
  (the two-universe rule); the result indices match the family index telescope
  in count (`:index_arity`) and in type (evaluating computed indices via NbE).
  """
  @spec check_ctor(Cure.Core.Env.t(), Inductive.family(), Inductive.ctor()) ::
          :ok | {:error, term()}
  def check_ctor(env, %{params: params, indices: index_tele, level: fam_level}, %{
        args: args,
        result_indices: result_indices
      }) do
    with {:ok, ctx_params} <- check_telescope(Context.empty(env), params),
         {:ok, ctx_full, field_levels} <- check_ctor_args(ctx_params, args),
         :ok <- check_field_levels(field_levels, fam_level),
         :ok <- check_result_indices(ctx_full, result_indices, index_tele) do
      :ok
    end
  end

  # -- helpers ----------------------------------------------------------------

  # Infer `term` and require its type to be a universe; return that level.
  defp infer_sort(ctx, term) do
    with {:ok, type_value} <- infer(ctx, term) do
      case type_value do
        {:vtype, level} -> {:ok, level}
        _ -> {:error, :not_a_type}
      end
    end
  end

  # Require a type value to be a Π; return its domain value + codomain closure.
  defp ensure_pi({:vpi, dom, cod_closure}), do: {:ok, dom, cod_closure}
  defp ensure_pi(_), do: {:error, :not_a_function}

  # Require a type value to be a Σ; return its domain value + codomain closure.
  defp ensure_sigma({:vsigma, dom, cod_closure}), do: {:ok, dom, cod_closure}
  defp ensure_sigma(_), do: {:error, :not_a_sigma}

  # Require a type value to be an equality; return its two endpoint values.
  defp ensure_eq({:veq, _ty, a_value, b_value}), do: {:ok, a_value, b_value}
  defp ensure_eq(_), do: {:error, :not_an_equality}

  # Check `args` against a dependent telescope, threading each evaluated arg so
  # later telescope types can depend on earlier args. Returns the arg values
  # (most-recent first) so a caller can continue (e.g. params then indices).
  defp check_spine(ctx, args, tele, init_vals) do
    if length(args) == length(tele) do
      do_spine(ctx, Enum.zip(args, tele), init_vals)
    else
      {:error, :arg_arity}
    end
  end

  defp do_spine(_ctx, [], vals), do: {:ok, vals}

  defp do_spine(ctx, [{arg, {_name, type_term}} | rest], vals) do
    expected = Eval.eval(type_term, vals)

    with :ok <- check(ctx, arg, expected) do
      do_spine(ctx, rest, [Eval.eval(arg, Context.env(ctx)) | vals])
    end
  end

  # Telescope well-formedness: each entry is a valid type; returns the context
  # extended by the whole telescope.
  defp check_telescope(ctx, []), do: {:ok, ctx}

  defp check_telescope(ctx, [{_name, type_term} | rest]) do
    with {:ok, _level} <- infer_sort(ctx, type_term) do
      type_value = Eval.eval(type_term, Context.env(ctx))
      check_telescope(Context.extend(ctx, type_value), rest)
    end
  end

  # Like check_telescope but also collects each field type's universe level.
  defp check_ctor_args(ctx, args) do
    Enum.reduce_while(args, {:ok, ctx, []}, fn {_name, type_term}, {:ok, c, levels} ->
      case infer_sort(c, type_term) do
        {:ok, level} ->
          c2 = Context.extend(c, Eval.eval(type_term, Context.env(c)))
          {:cont, {:ok, c2, [level | levels]}}

        err ->
          {:halt, err}
      end
    end)
  end

  defp check_field_levels(levels, fam_level) do
    if Enum.all?(levels, &(&1 <= fam_level)), do: :ok, else: {:error, :universe_level}
  end

  # Check a constructor application's args against its telescope (dependent),
  # returning the accumulated arg values (most-recent first) for result-index
  # computation. A failure on a data-typed argument is an index disagreement.
  defp check_ctor_app(ctx, args, tele) do
    if length(args) == length(tele) do
      check_ctor_app_rec(ctx, Enum.zip(args, tele), [])
    else
      {:error, :ctor_arity}
    end
  end

  defp check_ctor_app_rec(_ctx, [], vals), do: {:ok, vals}

  defp check_ctor_app_rec(ctx, [{arg, {_name, type_term}} | rest], vals) do
    expected = Eval.eval(type_term, vals)

    case check(ctx, arg, expected) do
      :ok -> check_ctor_app_rec(ctx, rest, [Eval.eval(arg, Context.env(ctx)) | vals])
      {:error, _} = err -> remap_index_error(err, expected)
    end
  end

  # A mismatch on a constructor argument whose expected type is a family value is
  # an index disagreement (the kernel-level backstop; the elaborator surfaces the
  # user-facing :index_unification earlier — see plan M3.4/M8.4).
  defp remap_index_error(_err, {:vdata, _name, _args}), do: {:error, :index_mismatch}
  defp remap_index_error(err, _expected), do: err

  # -- dependent case (§4.4) --------------------------------------------------

  # Apply a (curried) motive value to a list of argument values.
  defp apply_motive(motive_value, args),
    do: Enum.reduce(args, motive_value, fn arg, acc -> Eval.apply(acc, arg) end)

  # Extend `ctx` by a (dependent) telescope; return the new context and the fresh
  # neutral values bound for each telescope variable, in declaration order.
  defp extend_with_telescope(ctx, tele) do
    Enum.reduce(tele, {ctx, []}, fn {_name, type_term}, {c, vals} ->
      level = Context.length(c)
      type_value = Eval.eval(type_term, Context.env(c))
      {Context.extend(c, type_value), vals ++ [{:vneutral, {:nvar, level}}]}
    end)
  end

  # The motive must be a type family over the family's indices and the scrutinee:
  # applied to fresh indices ȷ̄ and x : D p̄ ȷ̄, its body must itself be a type.
  defp check_motive_wf(ctx, motive_value, %{name: dname, indices: index_tele}) do
    {ctx_indices, index_vals} = extend_with_telescope(ctx, index_tele)
    scrut_level = Context.length(ctx_indices)
    data_value = {:vdata, dname, index_vals}
    ctx_motive = Context.extend(ctx_indices, data_value)
    x_value = {:vneutral, {:nvar, scrut_level}}

    body_value = apply_motive(motive_value, index_vals ++ [x_value])

    case infer_type_value_sort(ctx_motive, body_value) do
      {:ok, _level} -> :ok
      _ -> {:error, :bad_motive}
    end
  end

  defp infer_type_value_sort(_ctx, {:vtype, level}), do: Universe.succ(level)
  defp infer_type_value_sort(_ctx, {:vint_type}), do: {:ok, 0}
  defp infer_type_value_sort(_ctx, {:vbool_type}), do: {:ok, 0}
  defp infer_type_value_sort(_ctx, {:vfloat_type}), do: {:ok, 0}

  defp infer_type_value_sort(ctx, {:vdata, name, _args}) do
    case Inductive.get_family(Context.signature(ctx), name) do
      nil -> {:error, {:unknown_family, name}}
      %{level: level} -> {:ok, level}
    end
  end

  defp infer_type_value_sort(ctx, {:vpi, _dom, _cod} = value) do
    value |> Quote.reify(Context.length(ctx)) |> infer_sort(ctx)
  end

  defp infer_type_value_sort(ctx, {:vsigma, _dom, _cod} = value) do
    value |> Quote.reify(Context.length(ctx)) |> infer_sort(ctx)
  end

  defp infer_type_value_sort(ctx, {:veq, _ty, _a, _b} = value) do
    value |> Quote.reify(Context.length(ctx)) |> infer_sort(ctx)
  end

  defp infer_type_value_sort(_ctx, _value), do: {:error, :not_a_type_value}

  # Every declared constructor of the family must have a branch (§7 coverage).
  defp check_coverage(sig, dname, branches) do
    declared = sig |> Inductive.ctors_of(dname) |> Enum.map(& &1.name) |> MapSet.new()
    covered = branches |> Enum.map(fn {c, _ar, _b} -> c end) |> MapSet.new()
    if MapSet.subset?(declared, covered), do: :ok, else: {:error, :coverage}
  end

  # Each branch body is checked under its constructor's telescope, against the
  # motive instantiated at that constructor's computed indices s̄ⱼ and value cⱼ āⱼ.
  defp check_case_branches(ctx, sig, motive_value, branches, scrut_indices) do
    Enum.reduce_while(branches, :ok, fn {cname, arity, body}, :ok ->
      case Inductive.get_ctor(sig, cname) do
        nil ->
          {:halt, {:error, {:unknown_ctor, cname}}}

        %{args: tele, result_indices: result_indices} when length(tele) == arity ->
          {ctx_branch, arg_vals} = extend_with_telescope(ctx, tele)
          subst = branch_index_subst(ctx, result_indices, scrut_indices, arity)
          ctx_branch = specialize_branch_context(ctx_branch, subst)
          # Result indices are written over the ctor's args (most-recent first).
          s_values = Enum.map(result_indices, &Eval.eval(&1, Enum.reverse(arg_vals)))
          ctor_value = {:vctor, cname, arg_vals}
          expected =
            motive_value
            |> apply_motive(s_values ++ [ctor_value])
            |> specialize_branch_value(ctx_branch, subst)

          case check(ctx_branch, body, expected) do
            :ok -> {:cont, :ok}
            {:error, _} -> {:halt, {:error, :branch_type}}
          end

        %{} ->
          {:halt, {:error, :branch_arity}}
      end
    end)
  end

  defp branch_index_subst(ctx, result_indices, scrut_indices, arity) do
    depth = Context.length(ctx)

    result_indices
    |> Enum.zip(scrut_indices)
    |> Enum.reduce(%{}, fn
      {{:var, i}, scrut_value}, acc ->
        replacement =
          scrut_value
          |> Quote.reify(depth)
          |> Term.shift(arity, 0)

        Map.put(acc, i, replacement)

      {_other, _scrut_value}, acc ->
        acc
    end)
  end

  defp specialize_branch_context(ctx, subst) when map_size(subst) == 0, do: ctx

  defp specialize_branch_context(ctx, subst) do
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

  defp specialize_branch_value(value, _ctx, subst) when map_size(subst) == 0, do: value

  defp specialize_branch_value(value, ctx, subst) do
    value
    |> Quote.reify(Context.length(ctx))
    |> replace_branch_vars(subst)
    |> Eval.eval(Context.env(ctx))
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
    do:
      {:data, n, Enum.map(ps, &replace_branch_vars(&1, subst)),
       Enum.map(is, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:ctor, n, args}, subst),
    do: {:ctor, n, Enum.map(args, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:case, scr, m, brs}, subst),
    do:
      {:case, replace_branch_vars(scr, subst), replace_branch_vars(m, subst),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, replace_branch_vars(b, shift_subst(subst, ar))} end)}

  defp replace_branch_vars({:eq, t, a, b}, subst),
    do:
      {:eq, replace_branch_vars(t, subst), replace_branch_vars(a, subst),
       replace_branch_vars(b, subst)}

  defp replace_branch_vars({:refl, a}, subst), do: {:refl, replace_branch_vars(a, subst)}

  defp replace_branch_vars({:rewrite, p, m, b}, subst),
    do:
      {:rewrite, replace_branch_vars(p, subst), replace_branch_vars(m, subst),
       replace_branch_vars(b, subst)}

  defp replace_branch_vars({:prim, op, args}, subst),
    do: {:prim, op, Enum.map(args, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars(other, _subst), do: other

  defp shift_subst(subst, amount) do
    Map.new(subst, fn {k, v} -> {k + amount, Term.shift(v, amount, 0)} end)
  end

  defp check_result_indices(ctx_full, result_indices, index_tele) do
    if length(result_indices) == length(index_tele) do
      case do_spine(ctx_full, Enum.zip(result_indices, index_tele), []) do
        {:ok, _vals} -> :ok
        err -> err
      end
    else
      {:error, :index_arity}
    end
  end

  # Cumulative subtyping: universe-level inclusion on sorts, conversion otherwise.
  # Arithmetic: numeric-polymorphic (Int or Float), result matches the operands.
  defp infer_prim(ctx, op, [a, b]) when op in [:add, :sub, :mul, :div] do
    with {:ok, ta} <- infer(ctx, a),
         true <- numeric_type?(ta),
         :ok <- check(ctx, b, ta) do
      {:ok, ta}
    else
      _ -> {:error, {:prim_type, op}}
    end
  end

  # Integer remainder.
  defp infer_prim(ctx, :rem, [a, b]) do
    with :ok <- check(ctx, a, {:vint_type}), :ok <- check(ctx, b, {:vint_type}) do
      {:ok, {:vint_type}}
    else
      _ -> {:error, {:prim_type, :rem}}
    end
  end

  # Ordered comparison: numeric operands, boolean result.
  defp infer_prim(ctx, op, [a, b]) when op in [:lt, :le, :gt, :ge] do
    with {:ok, ta} <- infer(ctx, a),
         true <- numeric_type?(ta),
         :ok <- check(ctx, b, ta) do
      {:ok, {:vbool_type}}
    else
      _ -> {:error, {:prim_type, op}}
    end
  end

  # Equality: any shared type, boolean result.
  defp infer_prim(ctx, op, [a, b]) when op in [:eq, :ne] do
    with {:ok, ta} <- infer(ctx, a), :ok <- check(ctx, b, ta) do
      {:ok, {:vbool_type}}
    else
      _ -> {:error, {:prim_type, op}}
    end
  end

  # Boolean connectives.
  defp infer_prim(ctx, op, [a, b]) when op in [:and, :or] do
    with :ok <- check(ctx, a, {:vbool_type}), :ok <- check(ctx, b, {:vbool_type}) do
      {:ok, {:vbool_type}}
    else
      _ -> {:error, {:prim_type, op}}
    end
  end

  defp infer_prim(ctx, :not, [a]) do
    with :ok <- check(ctx, a, {:vbool_type}) do
      {:ok, {:vbool_type}}
    else
      _ -> {:error, {:prim_type, :not}}
    end
  end

  # Numeric negation: numeric operand, same result type.
  defp infer_prim(ctx, :neg, [a]) do
    with {:ok, ta} <- infer(ctx, a), true <- numeric_type?(ta) do
      {:ok, ta}
    else
      _ -> {:error, {:prim_type, :neg}}
    end
  end

  defp infer_prim(_ctx, op, _args), do: {:error, {:unknown_prim, op}}

  defp numeric_type?({:vint_type}), do: true
  defp numeric_type?({:vfloat_type}), do: true
  defp numeric_type?(_), do: false

  defp subtype?({:vtype, l1}, {:vtype, l2}, _ctx), do: Universe.le?(l1, l2)

  defp subtype?(inferred, expected, ctx),
    do: Conv.conv_values?(inferred, expected, Context.length(ctx), Context.signature(ctx))
end
