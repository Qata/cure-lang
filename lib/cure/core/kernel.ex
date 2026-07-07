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

  alias Cure.Core.{Certificate, Context, Conv, Env, Eval, Inductive, Normalise, Quote, Term, Universe}

  @type result :: {:ok, Cure.Core.Value.t()} | {:error, term()}

  @doc """
  Normalize `term` in `ctx` via the shared trusted Core normalizer
  (`Cure.Core.Normalise`).

  Full normal form under the certified δ gate, preserving stuck `case`
  (`stuck_cases: :preserve`): it unfolds certified global heads and reduces β/ι
  redexes but does not recurse into the branch bodies of a neutral case — which
  keeps recursive certified definitions from expanding forever while still
  exposing the definitional equalities the surface proof elaborator needs.
  """
  @spec normalize(Context.t(), Cure.Core.Term.t()) :: Cure.Core.Term.t() | :fuel_exhausted
  def normalize(ctx, term), do: Normalise.nf(ctx, term)

  @doc "Normalize `term` in `ctx` via the shared trusted Core normalizer, with options."
  @spec normalize(Context.t(), Cure.Core.Term.t(), Normalise.opts()) :: Cure.Core.Term.t() | :fuel_exhausted
  def normalize(ctx, term, opts), do: Normalise.nf(ctx, term, opts)
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
  def infer(_ctx, {:float_type}), do: {:ok, {:vtype, 0}}
  def infer(_ctx, {:float_lit, _f}), do: {:ok, {:vfloat_type}}

  # {:absurd} is an elaborator-only marker sitting in a discharged (unreachable)
  # case branch, which check_case_branches never checks. It has no positive typing
  # rule; a reachable occurrence fails cleanly here rather than crashing the kernel
  # with an unmatched-clause exception (spec §5/§8.1).
  def infer(_ctx, {:absurd}), do: {:error, :absurd_in_reachable_position}

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

      %{args: tele, result_indices: result_indices} = ctor_sig ->
        family_name = Inductive.ctor_family(sig, name)
        result_params = Map.get(ctor_sig, :result_params, [])

        if Inductive.param_count(sig, family_name) > 0 do
          # Parameters are implicit; nothing in a bare {:ctor,…} term carries
          # them (only the untrusted elaborator's metavariable solver does, which
          # the kernel does not trust). A param-bearing constructor must be
          # type-CHECKED against an expected vdata that supplies the parameters —
          # see the check/3 clause below.
          {:error, {:ctor_requires_checking_mode, family_name}}
        else
          with {:ok, arg_env} <- check_ctor_app(ctx, [], args, tele) do
            # The accumulated arg values (most-recent first) are exactly the env
            # in which the result terms are written; compute them by NbE (so a
            # computed index like `and(d1,d2)` reduces once δ is available, M7).
            param_values = Enum.map(result_params, &Eval.eval(&1, arg_env))
            index_values = Enum.map(result_indices, &Eval.eval(&1, arg_env))
            {:ok, {:vdata, family_name, param_values ++ index_values}}
          end
        end
    end
  end

  def infer(ctx, {:case, scrut, motive, branches}) do
    sig = Context.signature(ctx)

    case infer(ctx, scrut) do
      {:ok, {:vdata, dname, scrut_args}} ->
        family = Inductive.get_family(sig, dname)
        # {:vdata} carries params ++ indices; the motive and the branch-index
        # unifier range over indices only, so split the params off up front.
        pc = Inductive.param_count(sig, dname)
        {scrut_params, scrut_idx} = Enum.split(scrut_args, pc)
        motive_value = Eval.eval(motive, Context.env(ctx))

        with :ok <- check_motive_wf(ctx, motive_value, family, scrut_params),
             :ok <- check_coverage(ctx, sig, dname, branches, scrut_idx),
             :ok <-
               check_case_branches(
                 ctx,
                 sig,
                 dname,
                 motive_value,
                 branches,
                 scrut_idx,
                 scrut_params
               ) do
          # Result type = motive at the scrutinee's actual indices and value (§4.4).
          scrut_value = Eval.eval(scrut, Context.env(ctx))
          {:ok, apply_motive(motive_value, scrut_idx ++ [scrut_value])}
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

  # Checking-mode constructor application: the expected vdata supplies the
  # family's parameters (which pure inference cannot source), so this is the path
  # a param-bearing constructor takes (from check_def's top-level check and from
  # check_case_branches' per-branch check). `:vdata` is a 3-tuple carrying a
  # single combined `params ++ indices` list; split off the params by param_count
  # to seed check_ctor_app, then re-derive the actual result and compare it to
  # `expected` (arguments checking against their own types is NOT enough — the
  # computed indices must still match the expected type's).
  def check(ctx, {:ctor, cname, args}, {:vdata, family, combined_args} = expected) do
    sig = Context.signature(ctx)
    pc = Inductive.param_count(sig, family)
    {params, _indices} = Enum.split(combined_args, pc)

    case Inductive.get_ctor(sig, cname) do
      nil ->
        {:error, {:unknown_ctor, cname}}

      %{args: tele, result_indices: result_indices} = ctor_sig ->
        result_params = Map.get(ctor_sig, :result_params, [])

        if Inductive.ctor_family(sig, cname) != family do
          {:error, {:foreign_ctor, cname}}
        else
          with {:ok, arg_env} <- check_ctor_app(ctx, params, args, tele) do
            actual_params = Enum.map(result_params, &Eval.eval(&1, arg_env))
            actual_indices = Enum.map(result_indices, &Eval.eval(&1, arg_env))
            actual = {:vdata, family, actual_params ++ actual_indices}

            if Conv.conv_values?(actual, expected, Context.length(ctx), sig) do
              :ok
            else
              {:error, {:conversion_failure, actual, expected}}
            end
          end
        end
    end
  end

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

        with {:ok, _level} <- infer_sort(ctx, type_term),
             :ok <- check(ctx, body_term, Eval.eval(type_term, [])),
             :ok <- run_final_core_validator(type_term, body_term) do
          :ok
        end
    end
  end

  # Final-Core grammar-boundary instrumentation (K11a). Scans BOTH the declared
  # type and the body — a legacy node in a signature is as much a checklist hit
  # as one in the body. Emits warnings via the pipeline and rejects only clauses
  # configured to :reject (none, by Wave-0 default); on a mixed verdict,
  # rejections from either term are combined.
  defp run_final_core_validator(type_term, body_term) do
    cfg = Cure.Core.Validator.check_def_config()

    case {Cure.Core.Validator.validate(type_term, cfg), Cure.Core.Validator.validate(body_term, cfg)} do
      {{:ok, w1}, {:ok, w2}} ->
        Enum.each(w1 ++ w2, fn d ->
          Cure.Pipeline.Events.emit(
            :kernel,
            :final_core_violation,
            %{clause: d.clause, message: d.message},
            %{}
          )
        end)

        :ok

      {{:error, r1}, {:ok, _}} -> {:error, {:final_core_violation, r1}}
      {{:ok, _}, {:error, r2}} -> {:error, {:final_core_violation, r2}}
      {{:error, r1}, {:error, r2}} -> {:error, {:final_core_violation, r1 ++ r2}}
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
  def check_ctor(env, %{name: fname, params: params, indices: index_tele, level: fam_level}, ctor) do
    %{args: args, result_indices: result_indices} = ctor
    result_params = Map.get(ctor, :result_params, [])

    with {:ok, ctx_params} <- check_telescope(Context.empty(env), params),
         {:ok, ctx_full, field_levels} <- check_ctor_args(ctx_params, args),
         :ok <- check_field_levels(field_levels, fam_level),
         :ok <-
           check_uniform_params(fname, ctor.name, result_params, length(params), length(args)),
         :ok <-
           check_result_indices(ctx_full, Context.env(ctx_params), result_indices, index_tele) do
      :ok
    end
  end

  # Each result parameter must be exactly the family's corresponding parameter
  # variable, as a de Bruijn var in ctx_full = params(outer) ++ args(inner): the
  # p-th declared parameter is {:var, num_args + (num_params - 1 - p)}. A ctor
  # that writes anything else in a parameter position (a non-uniform parameter)
  # is rejected — that position would have to be refined by matching, which is
  # index behaviour, not parameter behaviour.
  defp check_uniform_params(fname, cname, result_params, num_params, num_args) do
    cond do
      length(result_params) != num_params ->
        {:error, {:non_uniform_parameter, %{family: fname, ctor: cname, position: :arity}}}

      true ->
        result_params
        |> Enum.with_index()
        |> Enum.reduce_while(:ok, fn {term, p}, :ok ->
          expected = {:var, num_args + (num_params - 1 - p)}

          if term == expected,
            do: {:cont, :ok},
            else:
              {:halt,
               {:error, {:non_uniform_parameter, %{family: fname, ctor: cname, position: p}}}}
        end)
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
  # The inductive identity type `Eq(a, x, y)` (spec 2026-07-04) evaluates to a
  # `{:vdata, :Eq, [a, x, y]}` value (1 parameter + 2 indices); its endpoints are
  # the two indices. The primitive `{:veq}` form is still produced by the internal
  # rewrite machinery (retired in a later phase), so both are accepted here.
  defp ensure_eq({:veq, _ty, a_value, b_value}), do: {:ok, a_value, b_value}
  defp ensure_eq({:vdata, :Eq, [_ty, a_value, b_value]}), do: {:ok, a_value, b_value}
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
  defp check_ctor_app(ctx, param_vals, args, tele) do
    if length(args) == length(tele) do
      # Seed the local evaluation environment with the family's actual parameter
      # values (most-recent-first, mirroring check_ctor's ctx_full = params ++
      # args numbering) so a ctor arg whose declared type references a parameter
      # (e.g. `prepend`'s `x : a`) resolves to the real parameter, not a bogus
      # out-of-range neutral.
      check_ctor_app_rec(ctx, Enum.zip(args, tele), Enum.reverse(param_vals))
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
  #
  # `param_vals` seeds the *isolated* local evaluation environment for `tele`'s
  # own type terms (mirroring check_ctor's ctx_full = params ++ args numbering) —
  # NOT the ambient `ctx`, which has an unrelated numbering. Each entry may still
  # reference earlier entries of the same `tele` (threaded via the same local
  # list). `ctx` is extended in parallel purely to keep the ambient context's
  # depth/levels consistent for whatever uses the returned context afterward
  # (e.g. checking a branch body, which IS written relative to the ambient ctx).
  defp extend_with_telescope(ctx, tele, param_vals \\ []) do
    {ctx_final, _local_vals, fresh_vals} =
      Enum.reduce(tele, {ctx, Enum.reverse(param_vals), []}, fn {_name, type_term},
                                                                {c, local_vals, fresh} ->
        level = Context.length(c)
        type_value = Eval.eval(type_term, local_vals)
        fresh_val = {:vneutral, {:nvar, level}}
        {Context.extend(c, type_value), [fresh_val | local_vals], fresh ++ [fresh_val]}
      end)

    {ctx_final, fresh_vals}
  end

  # The motive must be a type family over the family's indices and the scrutinee:
  # applied to fresh indices ȷ̄ and x : D p̄ ȷ̄, its body must itself be a type.
  # The scrutinee's actual parameters (`scrut_params`) are fixed context: they
  # seed the index telescope's own evaluation (an index type may mention a
  # parameter) and fill the parameter slots of the scrutinee's data value. Values
  # in this NbE representation reference free variables by absolute de Bruijn
  # LEVEL, so `scrut_params` need no shift as more binders are added.
  defp check_motive_wf(ctx, motive_value, %{name: dname, indices: index_tele}, scrut_params) do
    {ctx_indices, index_vals} = extend_with_telescope(ctx, index_tele, scrut_params)
    scrut_level = Context.length(ctx_indices)
    data_value = {:vdata, dname, scrut_params ++ index_vals}
    ctx_motive = Context.extend(ctx_indices, data_value)
    x_value = {:vneutral, {:nvar, scrut_level}}

    body_value = apply_motive(motive_value, index_vals ++ [x_value])

    case infer_type_value_sort(ctx_motive, body_value) do
      {:ok, _level} -> :ok
      _ -> {:error, :bad_motive}
    end
  end

  defp infer_type_value_sort(_ctx, {:vtype, level}), do: Universe.succ(level)

  # A neutral is a valid type of sort `sublevel` iff its own declared type in
  # `ctx` is itself `{:vtype, sublevel}` — i.e. the variable it stands for was
  # bound at a universe (e.g. a parameter `a : Type` used polymorphically as the
  # case result type). de Bruijn index of a level-`level` neutral is
  # `Context.length(ctx) - 1 - level`.
  defp infer_type_value_sort(ctx, {:vneutral, {:nvar, level}}) do
    idx = Context.length(ctx) - 1 - level

    case Context.lookup(ctx, idx) do
      {:vtype, sublevel} -> {:ok, sublevel}
      _ -> {:error, :not_a_type_value}
    end
  end

  defp infer_type_value_sort(_ctx, {:vint_type}), do: {:ok, 0}
  defp infer_type_value_sort(_ctx, {:vfloat_type}), do: {:ok, 0}

  defp infer_type_value_sort(ctx, {:vdata, name, _args}) do
    case Inductive.get_family(Context.signature(ctx), name) do
      nil -> {:error, {:unknown_family, name}}
      %{level: level} -> {:ok, level}
    end
  end

  # Π/Σ/Eq value clauses recurse on the sub-VALUES directly, mirroring `infer/2`'s
  # type-formation rules for the corresponding terms, instead of reifying and
  # re-inferring. `Quote.reify` collapses `{:vdata, name, args}` → `{:data, name,
  # args, []}` (it has no inductive signature to recover the param/index split), so
  # reifying a Π/Σ/Eq whose domain (or Eq carrier) is an INDEXED family loses the
  # split and re-inference fails with `:arg_arity` — a false `:bad_motive`. The
  # value-recursion is a faithful mirror: it bottoms out in the same
  # `infer_type_value_sort` clauses (including the direct `{:vdata,…}` clause that
  # already classifies bare indexed-family motive RESULTS), so acceptance is
  # exactly what a non-lossy reify+infer would decide, and a non-type domain still
  # falls through to `:not_a_type_value` (rejected, no false positives).
  defp infer_type_value_sort(ctx, {:vpi, dom, cod_closure}) do
    with {:ok, l1} <- infer_type_value_sort(ctx, dom) do
      fresh = {:vneutral, {:nvar, Context.length(ctx)}}
      cod_value = Eval.apply_closure(cod_closure, fresh)

      with {:ok, l2} <- infer_type_value_sort(Context.extend(ctx, dom), cod_value) do
        {:ok, Universe.max(l1, l2)}
      end
    end
  end

  defp infer_type_value_sort(ctx, {:vsigma, dom, cod_closure}) do
    with {:ok, l1} <- infer_type_value_sort(ctx, dom) do
      fresh = {:vneutral, {:nvar, Context.length(ctx)}}
      cod_value = Eval.apply_closure(cod_closure, fresh)

      with {:ok, l2} <- infer_type_value_sort(Context.extend(ctx, dom), cod_value) do
        {:ok, Universe.max(l1, l2)}
      end
    end
  end

  # Eq's type-formation rule (mirrors `infer/2`'s `{:eq, ty, a, b}` clause): its
  # sort is the sort of the carrier `ty`, and both endpoints must inhabit `ty`.
  # `ty`'s sort is inferred by value-recursion (robust to an indexed carrier); the
  # endpoints are reified and `check`ed against `ty`. Read-back is
  # SIGNATURE-AWARE (`Context.signature(ctx)`) so an endpoint that is an
  # indexed-family type value (e.g. `SNat(s)`) recovers its param/index split and
  # `check` sees the correct arity — without the signature the split collapses and
  # a well-formed indexed-family Eq motive is false-rejected `:bad_motive`.
  defp infer_type_value_sort(ctx, {:veq, ty, a, b}) do
    with {:ok, level} <- infer_type_value_sort(ctx, ty) do
      depth = Context.length(ctx)
      sig = Context.signature(ctx)

      with :ok <- check(ctx, Quote.reify(a, depth, sig), ty),
           :ok <- check(ctx, Quote.reify(b, depth, sig), ty) do
        {:ok, level}
      end
    end
  end

  defp infer_type_value_sort(_ctx, _value), do: {:error, :not_a_type_value}

  # Coverage (§7 / §E.2): every declared constructor must either HAVE a branch or
  # be provably IMPOSSIBLE at the scrutinee's actual indices (index-unification
  # failure). Omitting a constructor that could still match is a coverage error;
  # omitting one the kernel certifies impossible is the Agda/Idris index-
  # contradiction discipline — and is exactly what lets a provably-uninhabited
  # scrutinee be eliminated by an empty branch list (ex-falso, K4/§H), with no
  # `{:absurd}` term. Relies on `:impossible` being the certain non-unification
  # verdict (K5a-hardened): a merely `:undecided` omission is NOT accepted.
  defp check_coverage(ctx, sig, dname, branches, scrut_indices) do
    covered = branches |> Enum.map(fn {c, _ar, _b} -> c end) |> MapSet.new()

    uncovered =
      sig
      |> Inductive.ctors_of(dname)
      |> Enum.reject(fn c -> MapSet.member?(covered, c.name) end)

    if Enum.all?(uncovered, fn c ->
         unify_indices(ctx, c.result_indices, scrut_indices, length(c.args)) == :impossible
       end),
       do: :ok,
       else: {:error, :coverage}
  end

  # Each branch body is checked under its constructor's telescope, against the
  # motive instantiated at that constructor's computed indices s̄ⱼ and value cⱼ āⱼ.
  # A branch must name a constructor of the scrutinee's OWN family `dname`; a
  # constructor of any other family is ill-formed (it can never match), so it is
  # rejected before its body is checked (`:foreign_ctor`).
  defp check_case_branches(ctx, sig, dname, motive_value, branches, scrut_indices, scrut_params) do
    Enum.reduce_while(branches, :ok, fn {cname, arity, body}, :ok ->
      case Inductive.get_ctor(sig, cname) do
        nil ->
          {:halt, {:error, {:unknown_ctor, cname}}}

        ctor ->
          cond do
            Inductive.ctor_family(sig, cname) != dname ->
              {:halt, {:error, {:foreign_ctor, cname}}}

            length(ctor.args) != arity ->
              {:halt, {:error, :branch_arity}}

            true ->
              %{args: tele, result_indices: result_indices} = ctor

              case unify_indices(ctx, result_indices, scrut_indices, arity) do
                :impossible ->
                  {:cont, :ok}                         # unreachable branch: body NOT checked

                verdict ->
                  subst =
                    case verdict do
                      {:solved, s} -> s
                      :trivial -> %{}
                    end

                  {ctx_branch, arg_vals} = extend_with_telescope(ctx, tele, scrut_params)
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
              end
          end
      end
    end)
  end

  @doc """
  Public branch-refinement query (spec §3). Given the caller's `ctx`, the
  scrutinee's family `dname` and a branch constructor `cname`, plus the
  scrutinee's actual index **values** `scrut_indices`, return the same verdict
  `unify_indices/4` produces: `{:solved, subst} | :trivial | :impossible`, where
  `subst` is in the branch de Bruijn frame `ctor-args ++ outer`. The elaborator
  delegates to this instead of carrying its own weaker index unification. Adds no
  unification logic — it reuses the private `unify_indices/4`. Guards two misuse
  shapes rather than trusting the caller: an unknown constructor (`nil` from
  `get_ctor`) and a constructor that exists but belongs to a different family
  than `dname` (`Inductive.ctor_family/2` mismatch) both verdict `:impossible`
  rather than proceeding against the wrong schema. Both are impossible in
  practice given the elaborator's own pre-validation, but this is new trusted-
  kernel code and `dname` is part of the signature precisely to be checked, not
  merely documented.
  """
  @spec branch_unify(Context.t(), atom(), atom(), [Cure.Core.Value.t()]) ::
          {:solved, map()} | :trivial | :impossible
  def branch_unify(ctx, dname, cname, scrut_indices) do
    sig = Context.signature(ctx)

    with %{args: tele, result_indices: result_indices} <- Inductive.get_ctor(sig, cname),
         ^dname <- Inductive.ctor_family(sig, cname) do
      unify_indices(ctx, result_indices, scrut_indices, length(tele))
    else
      _ -> :impossible
    end
  end

  # Bidirectional first-order unification of a constructor's result-index vector
  # (`result_indices`, terms over the ctor telescope — vars < arity) against the
  # scrutinee's index vector (`scrut_indices`, outer-context values) in ctx_branch's
  # de Bruijn space (spec §4.3/§4.4). Verdict: {:solved, subst} | :trivial | :impossible.
  # :impossible fires on a definite rigid index-head clash or a same-key merge
  # conflict; uncertainty is always :undecided (never :impossible).
  defp unify_indices(ctx, result_indices, scrut_indices, arity) do
    # Index-vector arity is fixed by the family, so a length mismatch is a
    # definite non-unification — NOT something to silently truncate. `Enum.zip`
    # drops the tail of the longer list, which would ignore a surplus/missing
    # index and spuriously verdict :trivial/:solved (#573). Guard it first.
    if length(result_indices) != length(scrut_indices) do
      :impossible
    else
      outer_depth = Context.length(ctx)

      result_indices
      |> Enum.zip(scrut_indices)
      |> Enum.map(fn {r, s_val} ->
        {r, s_val |> Quote.reify(outer_depth) |> Term.shift(arity, 0)}
      end)
      |> reduce_index_pairs(%{}, arity)
    end
  end

  defp reduce_index_pairs([], subst, _arity),
    do: (if map_size(subst) == 0, do: :trivial, else: {:solved, subst})

  defp reduce_index_pairs([{r, s} | rest], subst, arity) do
    case unify_one(r, s, arity, subst) do
      :impossible -> :impossible
      {:ok, subst2} -> reduce_index_pairs(rest, subst2, arity)
      # Dropping an :undecided pair (skip it, keep `subst`) is SOUND, not a bug
      # (K5a #575, proven, do NOT "fix" into propagation): the trusted case-checker
      # skips a branch body ONLY on :impossible. Dropping :undecided never yields a
      # spurious :impossible (that verdict comes solely from a rigid clash in some
      # pair), so no live branch is skipped. And the retained `subst` holds only the
      # DECIDED equations — a subset of the truth — so the branch's `expected` type is
      # specialized LESS (more general), making body-checking STRICTER. The only
      # possible effect is a false REJECTION, never a false acceptance. Propagating
      # :undecided instead would drop these valid refinements and reject MORE.
      :undecided -> reduce_index_pairs(rest, subst, arity)
    end
  end

  # r-side vars are always < arity (ctor telescope); s-side vars always >= arity
  # (outer). Disjoint ranges ⇒ the solve direction is unambiguous.
  defp unify_one({:var, i}, s, arity, subst) when i < arity,
    do: bind_index(i, s, arity, subst)                  # ctor arg := scrutinee term (Box case / prior behavior)

  defp unify_one(r, {:var, j}, arity, subst) when j >= arity,
    do: bind_index(j, r, arity, subst)                  # outer index var := ctor result index (4.3)

  defp unify_one({:ctor, c, as}, {:ctor, c, bs}, arity, subst) when length(as) == length(bs),
    do: unify_spine(as, bs, arity, subst)

  # :data heads: compare the FLATTENED spine (params ++ indices); Quote.reify always
  # emits an empty `indices` list, so never split ps-vs-is (spec §4.3).
  defp unify_one({:data, n, ps, is}, {:data, n, ps2, is2}, arity, subst)
       when length(ps) + length(is) == length(ps2) + length(is2),
       do: unify_spine(ps ++ is, ps2 ++ is2, arity, subst)

  defp unify_one(r, s, _arity, subst) when r == s, do: {:ok, subst}   # syntactically equal → consistent

  defp unify_one(r, s, _arity, _subst) do
    cond do
      # Agda Cycle rule (Rules/LHS/Unify.hs 43-44, `ifOccursStronglyRigid`): the
      # equation `x =?= v` is absurd when the datatype variable `x` occurs STRONGLY
      # RIGID in `v` (reachable through ctor/data spines only), by acyclicity of the
      # inductive. Both directions, mirroring Agda's symmetric Var/Var dispatch.
      var_cycle?(r, s) -> :impossible
      var_cycle?(s, r) -> :impossible
      # Definite rigid head clash ⇒ impossible (Conflict rule); else conservative.
      rigid_index?(r) and rigid_index?(s) and head_key(r) != head_key(s) -> :impossible
      true -> :undecided
    end
  end

  # `v` (a datatype/index variable) occurs strongly rigid in `t` ⇒ `v =?= t` is a
  # cyclic, hence absurd, equation. False for a non-var LHS.
  defp var_cycle?({:var, k}, t), do: strongly_rigid_occurs?(k, t)
  defp var_cycle?(_, _), do: false

  defp unify_spine([], [], _arity, subst), do: {:ok, subst}
  defp unify_spine([a | as], [b | bs], arity, subst) do
    case unify_one(a, b, arity, subst) do
      :impossible -> :impossible
      {:ok, subst2} -> unify_spine(as, bs, arity, subst2)
      # :undecided dropped for the same proven-sound reason as reduce_index_pairs.
      :undecided -> unify_spine(as, bs, arity, subst)
    end
  end

  # A spine length mismatch is a definite non-unification, NOT success (K5a #574).
  # Unreachable today — both callers (unify_one's :ctor/:data clauses) guard equal
  # length and the recursion above stays in lockstep — but a catch-all returning
  # `{:ok, subst}` (success) is a soundness landmine for any future direct caller.
  defp unify_spine(_, _, _arity, _subst), do: :impossible

  # Add {key => term} after an occurs-check; on a same-key clash, resolve-before-bind.
  #
  # `term` is first CHASED through the current substitution to its representative
  # (`resolve_index_var`). This keeps `subst` a union-find forest — each key points
  # toward a representative, never into a cycle. In particular, when a second forced
  # equation would close a loop (`c : T(a,a,b,b)` matched against `T(i,j,j,i)` induces
  # both `j := i` and, later, `i := j`), the resolved `term` collapses to the same
  # representative as `key`, so the second edge becomes the no-op `key == rterm`
  # clause below instead of a cyclic `i↦j`/`j↦i` pair. Without this the per-key
  # `occurs_index?` guard (which only inspects a key against its OWN value) cannot see
  # the cross-key cycle, and `replace_branch_vars` would apply it as a variable SWAP
  # rather than collapsing `i ≡ j` (spec §4.1 multi-key-cycle obligation).
  defp bind_index(key, term, arity, subst) do
    rterm = resolve_index_var(term, subst, 0)

    cond do
      rterm == {:var, key} -> {:ok, subst}              # already same class ⇒ no-op (breaks cycles)
      strongly_rigid_occurs?(key, rterm) -> :impossible # Agda Cycle rule: absurd (acyclicity)
      occurs_index?(key, rterm) -> :undecided           # weakly-rigid cycle ⇒ conservative degrade
      Map.has_key?(subst, key) ->
        old = Map.get(subst, key)
        cond do
          old == rterm -> {:ok, subst}                  # consistent
          rigid_index?(old) and rigid_index?(rterm) and head_key(old) != head_key(rterm) ->
            :impossible                                 # same-key merge conflict ⇒ impossible
          true ->
            # Resolve-before-bind (Agda Solution step): the key is already pinned to
            # `old`, so this pair really asserts `old =? rterm`. Re-unify them; for two
            # distinct scrutinee vars this routes through unify_one clause 2 and binds
            # the outer var (a forced equation).
            unify_one(old, rterm, arity, subst)
        end
      true -> {:ok, Map.put(subst, key, rterm)}
    end
  end

  # Chase a `{:var, k}` through `subst` to its representative (a non-var term or an
  # unbound var). Depth-bounded purely as a defensive backstop — the forest invariant
  # maintained by `bind_index` means a real cycle never forms, so the bound is never hit.
  defp resolve_index_var({:var, k} = v, subst, depth) when depth < 100_000 do
    case Map.get(subst, k) do
      nil -> v
      next -> resolve_index_var(next, subst, depth + 1)
    end
  end

  defp resolve_index_var(t, _subst, _depth), do: t

  defp rigid_index?({:ctor, _, _}), do: true
  defp rigid_index?({:data, _, _, _}), do: true
  defp rigid_index?({:type, _}), do: true
  defp rigid_index?({:pi, _, _}), do: true
  defp rigid_index?({:sigma, _, _}), do: true
  defp rigid_index?({:int_type}), do: true
  defp rigid_index?({:float_type}), do: true
  defp rigid_index?({:int_lit, _}), do: true
  defp rigid_index?({:float_lit, _}), do: true
  defp rigid_index?(_), do: false

  defp head_key({:ctor, n, _}), do: {:ctor, n}
  defp head_key({:data, n, _, _}), do: {:data, n}
  defp head_key(t) when is_tuple(t), do: elem(t, 0)
  defp head_key(other), do: other

  # Conservative occurs-check: does {:var, key} appear anywhere in term? Ignores
  # binder-depth shifts (over-approximates ⇒ at worst a spurious :undecided, never
  # an unsound bind). Given disjoint ranges it effectively never fires on real input.
  defp occurs_index?(key, {:var, k}), do: k == key
  defp occurs_index?(key, t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&occurs_index?(key, &1))
  defp occurs_index?(key, l) when is_list(l), do: Enum.any?(l, &occurs_index?(key, &1))
  defp occurs_index?(_key, _), do: false

  # Agda Cycle rule (Rules/LHS/Unify.hs `ifOccursStronglyRigid` / `flexRigOccurrenceIn`):
  # does {:var, key} occur STRONGLY RIGID in `term` — an occurrence reachable through
  # constructor/data spines ONLY, never a defined-function application or other neutral?
  # If so, `key =?= term` is unsolvable by acyclicity of the inductive, so the branch is
  # :impossible. The soundness of firing here (vs a conservative :undecided) rests
  # entirely on the ctor/data-only descent: `x = S(x)` is absurd, but `x = f(x)` for a
  # DEFINED `f` is NOT — `f` might be the identity — and an `:app`/neutral head stops the
  # search, so the latter never fires. The top of `term` must itself be a rigid ctor/data
  # head: a bare-var top is an ordinary solve (`x =?= x` handled upstream), not a cycle.
  defp strongly_rigid_occurs?(key, {:ctor, _n, args}), do: Enum.any?(args, &rigid_path_occurs?(key, &1))
  defp strongly_rigid_occurs?(key, {:data, _n, ps, is}), do: Enum.any?(ps ++ is, &rigid_path_occurs?(key, &1))
  defp strongly_rigid_occurs?(_key, _), do: false

  # Occurs along a purely rigid (ctor/data) path: a var matches; descent continues
  # solely through ctor/data spines; ANY other node (:app, neutral, meta, …) breaks
  # strong rigidity and halts the search on that sub-branch (⇒ conservative).
  defp rigid_path_occurs?(key, {:var, k}), do: k == key
  defp rigid_path_occurs?(key, {:ctor, _n, args}), do: Enum.any?(args, &rigid_path_occurs?(key, &1))
  defp rigid_path_occurs?(key, {:data, _n, ps, is}), do: Enum.any?(ps ++ is, &rigid_path_occurs?(key, &1))
  defp rigid_path_occurs?(_key, _), do: false

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

  defp replace_branch_vars({:var, i}, subst), do: replace_branch_var(i, subst, 0)

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
    Map.new(subst, fn {k, v} -> {k + amount, Term.shift(v, amount, 0)} end)
  end

  defp replace_branch_var(i, subst, depth) when depth < 100_000 do
    case Map.get(subst, i) do
      nil -> {:var, i}
      {:var, ^i} -> {:var, i}
      {:var, j} -> replace_branch_var(j, subst, depth + 1)
      term -> replace_branch_vars(term, subst)
    end
  end

  defp replace_branch_var(i, _subst, _depth), do: {:var, i}

  # `param_vals` (most-recent-first = Context.env(ctx_params)) seeds the local
  # evaluation environment so an index-telescope type that references a family
  # PARAMETER (e.g. MyEq's `x : a`, `y : a`) resolves to the real parameter rather
  # than a bogus out-of-range neutral — the same seeding `check_ctor_app` performs
  # for the ctor-application path. Without it, a parameter reference in the second-
  # or-later index position mis-levels (`{:conversion_failure, {:var,1}, {:var,0}}`).
  defp check_result_indices(ctx_full, param_vals, result_indices, index_tele) do
    if length(result_indices) == length(index_tele) do
      case do_spine(ctx_full, Enum.zip(result_indices, index_tele), param_vals) do
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
  @doc """
  The type **value** denoting the canonical `Bool` inductive (`{:vdata, :Bool, []}`).
  Bool has no params/indices, so this is exactly what `infer({:ctor, :True/:False, []})`
  and `eval({:data, :Bool, [], []})` both produce. Public: the elaborator's
  literal/`:case` lowering shares this single closed form (no drift surface).
  """
  @spec bool_type_value(Env.t()) :: Cure.Core.Value.t()
  def bool_type_value(sig) do
    fid = Inductive.builtin(sig, :bool) || raise "builtin :bool not seeded (bootstrap/load-order bug)"
    {:vdata, fid, []}
  end

  defp infer_prim(ctx, op, [a, b]) when op in [:lt, :le, :gt, :ge] do
    with {:ok, ta} <- infer(ctx, a),
         true <- numeric_type?(ta),
         :ok <- check(ctx, b, ta) do
      {:ok, bool_type_value(Context.signature(ctx))}
    else
      _ -> {:error, {:prim_type, op}}
    end
  end

  # Equality: any shared type, boolean result. (Accepts two Bool-typed operands
  # too — see Eval.fold's Bool-operand equality clause.)
  defp infer_prim(ctx, op, [a, b]) when op in [:eq, :ne] do
    with {:ok, ta} <- infer(ctx, a), :ok <- check(ctx, b, ta) do
      {:ok, bool_type_value(Context.signature(ctx))}
    else
      _ -> {:error, {:prim_type, op}}
    end
  end

  # The Boolean connectives (`and`/`or`/`not`) are no longer primitives — they are
  # Std.Bool functions (`and`/`or`/`not`) that `case`-eliminate the inductive
  # Bool. A residual `{:prim, :and/:or/:not}` therefore falls through to the
  # `{:unknown_prim, op}` clause below (the desired rejection). `bool_type_value/1`
  # stays: the numeric comparisons above still return the inductive Bool through it.

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
