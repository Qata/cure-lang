defmodule Cure.Elab.MacroExpand do
  @moduledoc """
  Compile-time execution of Tier-3 `computed by` macro uses.

  This is frontend orchestration: it elaborates an elab reference, checks its
  application to a reflected `Std.Syntax` Core value, normalizes the result,
  and reflects the result back to surface AST. The resulting AST is still
  elaborated and kernel-checked by the ordinary declaration path.
  """

  alias Cure.Compiler.MacroSyntax
  alias Cure.Core.{Context, Kernel, Normalise}
  alias Cure.Elab.Elaborator

  @max_fuel 32
  @normalise_fuel 10_000

  @spec expand(term(), Cure.Core.Env.t()) :: {:ok, term()} | {:error, term()}
  def expand(ast, env), do: expand_node(ast, env, @max_fuel)

  @doc "True when an AST contains a deferred Tier-3 use-site."
  @spec contains_computed_use?(term()) :: boolean()
  def contains_computed_use?({:computed_use, _meta, _children}), do: true

  def contains_computed_use?(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&contains_computed_use?/1)

  def contains_computed_use?(term) when is_list(term), do: Enum.any?(term, &contains_computed_use?/1)
  def contains_computed_use?(term) when is_map(term), do: Enum.any?(term, fn {k, v} -> contains_computed_use?(k) or contains_computed_use?(v) end)
  def contains_computed_use?(_), do: false

  defp expand_node({:computed_use, meta, [elab, input]}, env, fuel) when fuel > 0 do
    with {:ok, expanded} <- execute(meta, elab, input, env),
         {:ok, expanded} <- expand_node(expanded, env, fuel - 1) do
      {:ok, expanded}
    end
  end

  defp expand_node({:computed_use, meta, _children}, _env, 0),
    do: {:error, {:computed_macro_error, meta, :expansion_depth_exceeded}}

  defp expand_node(term, env, fuel) when is_tuple(term) do
    with {:ok, values} <- expand_list(Tuple.to_list(term), env, fuel), do: {:ok, List.to_tuple(values)}
  end

  defp expand_node(term, env, fuel) when is_list(term), do: expand_list(term, env, fuel)

  defp expand_node(term, env, fuel) when is_map(term) do
    with {:ok, entries} <- expand_list(Map.to_list(term), env, fuel), do: {:ok, Map.new(entries)}
  end

  defp expand_node(term, _env, _fuel), do: {:ok, term}

  defp expand_list(items, env, fuel) do
    Enum.reduce_while(items, {:ok, []}, fn item, {:ok, acc} ->
      case expand_node(item, env, fuel) do
        {:ok, expanded} -> {:cont, {:ok, [expanded | acc]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, values} -> {:ok, Enum.reverse(values)}
      error -> error
    end
  end

  defp execute(meta, elab_ast, input_ast, env) do
    context = Context.empty(env)
    input_core = input_ast |> MacroSyntax.to_syntax() |> MacroSyntax.to_core()

    with {:ok, elab_core, _elab_type} <-
           Elaborator.elaborate_expr_typed(elab_ast, [], context, env),
         application = {:app, elab_core, input_core},
         {:ok, _result_type} <- Kernel.infer(context, application),
         result <- Normalise.nf(context, application, fuel: @normalise_fuel),
         {:ok, result_ast} <- decode_result(result) do
      {:ok, result_ast}
    else
      {:error, reason} -> {:error, {:computed_macro_error, meta, reason}}
      :fuel_exhausted -> {:error, {:computed_macro_error, meta, :normalization_fuel_exhausted}}
    end
  rescue
    error -> {:error, {:computed_macro_error, meta, {:host_exception, error.__struct__}}}
  end

  defp decode_result(result) do
    if result == :fuel_exhausted do
      {:error, :normalization_fuel_exhausted}
    else
      decode_result_term(result)
    end
  end

  defp decode_result_term(result) do
    case MacroSyntax.from_core(result) do
      {:error, reason} -> {:error, reason}
      repr -> {:ok, MacroSyntax.from_syntax(repr)}
    end
  end
end
