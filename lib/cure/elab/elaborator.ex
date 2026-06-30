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

  alias Cure.Core.{Env, Eval, Inductive}

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
