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

  @normalise_fuel 10_000
  # Termination is guaranteed by active-stack cycle detection. Production
  # expansion therefore has no arbitrary depth/size ceiling; embedders and
  # tests may still supply defensive finite limits explicitly.
  @default_limits [max_expansions: :infinity, max_nodes: :infinity]

  @spec expand(term(), Cure.Core.Env.t()) :: {:ok, term()} | {:error, term()}
  def expand(ast, env), do: expand(ast, env, [])

  @doc "Expand computed syntax recursively from the inside out under explicit budgets."
  @type expansion_frame :: %{
          keyword: String.t() | nil,
          line: non_neg_integer() | nil,
          col: non_neg_integer() | nil
        }

  @spec expand(term(), Cure.Core.Env.t(), keyword()) :: {:ok, term()} | {:error, term()}
  def expand(ast, env, opts) when is_list(opts) do
    limits = Keyword.merge(@default_limits, opts)

    state = %{
      expansions: 0,
      nodes: 0,
      active: MapSet.new(),
      path: [],
      context: Keyword.get(opts, :callback_context),
      limits: limits
    }

    case expand_node(ast, env, state) do
      {:ok, expanded, _state} -> {:ok, expanded}
      {:error, _} = error -> error
    end
  end

  @doc "True when an AST contains a deferred Tier-3 use-site."
  @spec contains_computed_use?(term()) :: boolean()
  def contains_computed_use?({:computed_use, _meta, _children}), do: true
  def contains_computed_use?({:quoted_syntax, _meta, _children}), do: false

  def contains_computed_use?(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&contains_computed_use?/1)

  def contains_computed_use?(term) when is_list(term), do: Enum.any?(term, &contains_computed_use?/1)

  def contains_computed_use?(term) when is_map(term),
    do: Enum.any?(term, fn {k, v} -> contains_computed_use?(k) or contains_computed_use?(v) end)

  def contains_computed_use?(_), do: false

  defp expand_node({:computed_use, meta, [elab, input]} = node, env, state) do
    with {:ok, state} <- visit_node(state),
         {:ok, [elab, input], state} <- expand_children([elab, input], env, state),
         {:ok, state} <- begin_expansion(node, state),
         state = push_expansion(node, state),
         meta =
           meta
           |> Keyword.put(:provenance, expansion_chain(state))
           |> put_expansion_context(state.context),
         {:ok, expanded} <- execute(meta, elab, input, env),
         {:ok, expanded, state} <- expand_node(expanded, env, state),
         {:ok, state} <- end_expansion(node, state) do
      {:ok, expanded, state}
    end
  end

  defp expand_node({:quoted_syntax, _meta, _children} = quoted, _env, state) do
    with {:ok, state} <- visit_node(state), do: {:ok, quoted, state}
  end

  defp expand_node(term, env, state) when is_tuple(term) do
    with {:ok, values, state} <- expand_children(Tuple.to_list(term), env, state),
         {:ok, state} <- visit_node(state) do
      {:ok, List.to_tuple(values), state}
    end
  end

  defp expand_node(term, env, state) when is_list(term), do: expand_children(term, env, state)

  defp expand_node(term, env, state) when is_map(term) do
    with {:ok, entries, state} <- expand_children(Map.to_list(term), env, state),
         {:ok, state} <- visit_node(state) do
      {:ok, Map.new(entries), state}
    end
  end

  defp expand_node(term, _env, state) do
    with {:ok, state} <- visit_node(state), do: {:ok, term, state}
  end

  defp expand_children(items, env, state) do
    Enum.reduce_while(items, {:ok, [], state}, fn item, {:ok, acc, state} ->
      case expand_node(item, env, state) do
        {:ok, expanded, state} -> {:cont, {:ok, [expanded | acc], state}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, values, state} -> {:ok, Enum.reverse(values), state}
      error -> error
    end
  end

  defp visit_node(%{nodes: nodes, limits: limits} = state) do
    nodes = nodes + 1

    if over_limit?(nodes, Keyword.fetch!(limits, :max_nodes)),
      do: {:error, budget_error(:node_count, state)},
      else: {:ok, %{state | nodes: nodes}}
  end

  defp begin_expansion(node, %{expansions: expansions, active: active, limits: limits} = state) do
    key = expansion_key(node)
    frame = expansion_frame(node)

    if MapSet.member?(active, key) do
      {:error, {:macro_expansion_cycle, Enum.reverse([frame | state.path])}}
    else
      expansions = expansions + 1

      if over_limit?(expansions, Keyword.fetch!(limits, :max_expansions)) do
        {:error, {:macro_expansion_budget, :expansion_count, Enum.reverse([frame | state.path])}}
      else
        {:ok, %{state | expansions: expansions, active: MapSet.put(active, key)}}
      end
    end
  end

  defp push_expansion(node, state),
    do: %{state | path: [expansion_frame(node) | state.path]}

  defp end_expansion(node, %{active: active, path: [_frame | path]} = state),
    do: {:ok, %{state | active: MapSet.delete(active, expansion_key(node)), path: path}}

  defp end_expansion(node, %{active: active} = state),
    do: {:ok, %{state | active: MapSet.delete(active, expansion_key(node))}}

  defp budget_error(kind, state), do: {:macro_expansion_budget, kind, expansion_chain(state)}

  defp expansion_chain(%{path: path}), do: Enum.reverse(path)

  defp put_expansion_context(meta, nil), do: meta
  defp put_expansion_context(meta, context), do: Keyword.put(meta, :expansion_context, context)

  defp over_limit?(_value, :infinity), do: false
  defp over_limit?(value, limit) when is_integer(limit), do: value > limit

  defp over_limit?(_value, limit),
    do: raise(ArgumentError, "macro expansion limit must be :infinity or a non-negative integer, got #{inspect(limit)}")

  # Ignore source positions in the active key. A recursive macro that rebuilds
  # its own use-site with fresh line/column metadata is still the same expansion
  # node and must be rejected; two sibling nodes remain distinct by their input.
  defp expansion_key({:computed_use, meta, [elab, input]}) do
    {Keyword.get(meta, :keyword), MacroSyntax.to_syntax(elab), MacroSyntax.to_syntax(input)}
  end

  defp expansion_key(node), do: node

  defp expansion_frame({:computed_use, meta, _}) do
    %{
      keyword: Keyword.get(meta, :keyword),
      line: Keyword.get(meta, :line),
      col: Keyword.get(meta, :col)
    }
  end

  defp expansion_frame(_), do: %{keyword: nil, line: nil, col: nil}

  defp execute(meta, elab_ast, input_ast, env) do
    context = Context.empty(env)

    # The elab sees WHERE it was invoked, not just what it was handed: the
    # callback context travels with the input, as an attribute of the generic
    # `Syntax` node and as the derived record's trailing `context` field.
    input_repr =
      input_ast
      |> MacroSyntax.to_syntax()
      |> MacroSyntax.with_context(Keyword.get(meta, :expansion_context))

    input_cores =
      case Keyword.get(meta, :syntax_type) do
        nil ->
          [MacroSyntax.to_core(input_repr)]

        syntax_type ->
          [
            MacroSyntax.to_core_record(syntax_type, Keyword.get(meta, :syntax_fields, []), input_repr),
            MacroSyntax.to_core(input_repr)
          ]
      end

    with {:ok, elab_core, _elab_type} <-
           Elaborator.elaborate_expr_typed(elab_ast, [], context, env),
         {:ok, result_ast} <- execute_application(context, elab_core, input_cores) do
      {:ok, result_ast}
    else
      {:error, reason} -> {:error, {:computed_macro_error, meta, reason}}
      :fuel_exhausted -> {:error, {:computed_macro_error, meta, :normalization_fuel_exhausted}}
    end
  rescue
    error -> {:error, {:computed_macro_error, meta, {:host_exception, error.__struct__}}}
  end

  defp execute_application(context, elab_core, [input_core | fallback]) do
    application = {:app, elab_core, input_core}

    case Kernel.infer(context, application) do
      {:ok, _result_type} ->
        result = Normalise.nf(context, application, fuel: @normalise_fuel)
        decode_result(result)

      {:error, {:foreign_ctor, _}} when fallback != [] ->
        execute_application(context, elab_core, fallback)

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp execute_application(_context, _elab_core, []),
    do: {:error, :no_compatible_macro_input}

  defp decode_result(result) do
    if result == :fuel_exhausted do
      {:error, :normalization_fuel_exhausted}
    else
      decode_result_term(result)
    end
  end

  defp decode_result_term(result) do
    case MacroSyntax.from_core(result) do
      {:error, reason} ->
        {:error, reason}

      {:syn_failure, name, args} ->
        {:error, {:author_failure, Atom.to_string(name), Enum.map(args, &MacroSyntax.from_syntax/1)}}

      repr ->
        {:ok, MacroSyntax.from_syntax(repr)}
    end
  end
end
