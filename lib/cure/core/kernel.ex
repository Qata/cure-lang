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

  alias Cure.Core.{Context, Conv, Eval, Inductive, Quote, Universe}

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

  @doc "Check `term` against the expected type value in `ctx`."
  @spec check(Context.t(), Cure.Core.Term.t(), Cure.Core.Value.t()) :: :ok | {:error, term()}
  # Bidirectional rule: a lambda is checked against a Π, propagating the expected
  # domain into the body (more robust than infer when the body is not standalone).
  def check(ctx, {:lam, dom, body}, {:vpi, exp_dom, cod_closure}) do
    dom_value = Eval.eval(dom, Context.env(ctx))

    if Conv.conv_values?(dom_value, exp_dom, Context.length(ctx)) do
      fresh = {:vneutral, {:nvar, Context.length(ctx)}}
      cod_value = Eval.apply_closure(cod_closure, fresh)
      check(Context.extend(ctx, exp_dom), body, cod_value)
    else
      {:error, :domain_mismatch}
    end
  end

  def check(ctx, term, expected) do
    with {:ok, inferred} <- infer(ctx, term) do
      if subtype?(inferred, expected, ctx), do: :ok, else: {:error, :type_mismatch}
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
  defp subtype?({:vtype, l1}, {:vtype, l2}, _ctx), do: Universe.le?(l1, l2)

  defp subtype?(inferred, expected, ctx),
    do: Conv.conv_values?(inferred, expected, Context.length(ctx))
end
