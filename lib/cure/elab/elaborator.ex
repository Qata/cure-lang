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

    if Inductive.get_ctor(env, atom) do
      with {:ok, present} <- map_present_args(args, names, ctx, env) do
        elaborate_ctor_app(env, atom, present)
      end
    else
      # Non-constructor application: elaborate to a term, then let the kernel type it.
      with {:ok, term} <- elaborate_expr({:function_call, [name: name], args}, names, env),
           {:ok, type} <- Kernel.infer(ctx, term) do
        {:ok, term, type}
      end
    end
  end

  def elaborate_expr_typed(other, names, ctx, env) do
    with {:ok, term} <- elaborate_expr(other, names, env),
         {:ok, type} <- Kernel.infer(ctx, term) do
      {:ok, term, type}
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
        {:vdata, dname, _indices} ->
          family = Inductive.get_family(env, dname)
          motive = build_constant_motive(dname, family.indices, result_type_term)

          with {:ok, branches} <- elaborate_branches(arms, ctx, env) do
            {:ok, {:case, scrut_term, motive, branches}}
          end

        _ ->
          {:error, :match_scrutinee_not_data}
      end
    end
  end

  # motive = λ(i₀:T₀)…λ(iₙ:Tₙ).λ(x : D ī). ResultType  (ResultType lifted over the
  # n index binders + the scrutinee binder).
  defp build_constant_motive(dname, index_tele, result_type_term) do
    n = length(index_tele)
    index_types = Enum.map(index_tele, &elem(&1, 1))
    scrut_type = {:data, dname, [], Enum.map((n - 1)..0//-1, &{:var, &1})}
    body = Subst.shift(result_type_term, n + 1, 0)

    (index_types ++ [scrut_type])
    |> Enum.reverse()
    |> Enum.reduce(body, fn type, acc -> {:lam, type, acc} end)
  end

  defp elaborate_branches(arms, ctx, env) do
    Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, arm_meta, body}, {:ok, acc} ->
      pattern = Keyword.fetch!(arm_meta, :pattern)

      case elaborate_branch(pattern, single_body(body), ctx, env) do
        {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp elaborate_branch(pattern, body_expr, ctx, env) do
    {cname, pattern_vars} = constructor_pattern(pattern)

    case Inductive.get_ctor(env, cname) do
      nil ->
        {:error, {:unknown_pattern_constructor, cname}}

      %{args: telescope, quantities: quantities} ->
        branch_names = branch_scope(quantities, pattern_vars)
        branch_ctx = extend_context(ctx, telescope)

        with {:ok, body_term, _type} <- elaborate_expr_typed(body_expr, branch_names, branch_ctx, env) do
          {:ok, {cname, length(telescope), body_term}}
        end
    end
  end

  defp constructor_pattern({:function_call, meta, args}) do
    cname = meta |> Keyword.fetch!(:name) |> String.to_atom()
    vars = Enum.map(args, fn {:variable, _meta, v} -> v end)
    {cname, vars}
  end

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

  defp extend_context(ctx, telescope) do
    Enum.reduce(telescope, ctx, fn {_name, type_term}, c ->
      Context.extend(c, Eval.eval(type_term, Context.env(c)))
    end)
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
      telescope = Enum.zip(ctor.args, ctor.quantities)
      init = {:ok, MetaCtx.new(), [], present_args}

      telescope
      |> Enum.reduce_while(init, &solve_arg/2)
      |> finish_ctor_app(cname, family, ctor)
    end
  end

  # One telescope slot: erased → fresh meta; present → unify expected vs actual.
  defp solve_arg({{_name, type_term}, :erased}, {:ok, mctx, chosen, present}) do
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

  defp finish_ctor_app({:error, _} = err, _cname, _family, _ctor), do: err

  defp finish_ctor_app({:ok, _mctx, _chosen, [_ | _]}, _cname, _family, _ctor),
    do: {:error, :too_many_arguments}

  defp finish_ctor_app({:ok, mctx, chosen, []}, cname, family, ctor) do
    args = Enum.map(chosen, &Unify.zonk(&1, mctx))

    if Enum.any?(args, &has_meta?/1) do
      {:error, {:unsolved_metavariables, cname}}
    else
      indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, args))
      result_type = Eval.eval({:data, family, [], indices}, [])
      {:ok, {:ctor, cname, args}, result_type}
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

    with {:ok, head} <- elaborate_expr({:variable, [], name}, scope, env),
         {:ok, core_args} <- map_elaborate(args, scope, env, &elaborate_expr/3) do
      {:ok, Enum.reduce(core_args, head, fn arg, acc -> {:app, acc, arg} end)}
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
