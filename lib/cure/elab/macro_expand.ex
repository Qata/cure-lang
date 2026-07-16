defmodule Cure.Elab.MacroExpand do
  @moduledoc """
  Compile-time execution of Tier-3 `computed by` macro uses.

  This is frontend orchestration: it elaborates an elab reference, checks its
  application to a reflected `Std.Syntax` Core value, normalizes the result,
  and reflects the result back to surface AST. The resulting AST is still
  elaborated and kernel-checked by the ordinary declaration path.
  """

  alias Cure.Compiler.{MacroFamily, MacroSyntax, Parser}
  alias Cure.Core.{Context, Kernel, Normalise}
  alias Cure.Elab.{Elaborator, TotalityClosure}

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
      fresh_counter: 0,
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
         {:ok, expanded, fresh_counter} <- execute(meta, elab, input, env, state.fresh_counter),
         state = %{state | fresh_counter: fresh_counter},
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

  defp execute(meta, elab_ast, input_ast, env, fresh_counter) do
    context = Context.empty(env)

    # The elab sees WHERE it was invoked, not just what it was handed: the
    # callback context travels with the input, as an attribute of the generic
    # `Syntax` node and as the derived record's trailing `context` field.
    input_repr =
      input_ast
      |> MacroSyntax.to_syntax()
      |> MacroSyntax.with_context(Keyword.get(meta, :expansion_context))

    field_types = resolve_field_types(Keyword.get(meta, :syntax_field_types, %{}), env)

    input_cores =
      case Keyword.get(meta, :syntax_type) do
        nil ->
          [[MacroSyntax.to_core(input_repr)]]

        syntax_type ->
          record =
            MacroSyntax.to_core_record(
              Cure.Core.Env.resolve_key(env, env.ctors, syntax_type),
              Keyword.get(meta, :syntax_fields, []),
              Keyword.get(meta, :syntax_repeated_fields, []),
              input_repr,
              field_types
            )

          direct =
            if Keyword.get(meta, :direct_inputs, false) or primitive_field_types?(field_types),
              do: direct_input_cores(input_repr, Keyword.get(meta, :syntax_fields, []), field_types),
              else: []

          Enum.filter([direct, [record], [MacroSyntax.to_core(input_repr)]], &(&1 != []))
      end

    with {:ok, elab_core, _elab_type} <-
           Elaborator.elaborate_expr_typed(elab_ast, [], context, env),
         {:ok, eval_env} <- TotalityClosure.certify_roots(env, global_names(elab_core)),
         {:ok, result_ast} <- execute_application(Context.empty(eval_env), elab_core, input_cores),
         {result_ast, fresh_counter} <- Parser.freshen_generated(result_ast, fresh_counter) do
      {:ok, result_ast, fresh_counter}
    else
      {:error, reason} -> {:error, {:computed_macro_error, meta, reason}}
      :fuel_exhausted -> {:error, {:computed_macro_error, meta, :normalization_fuel_exhausted}}
    end
  rescue
    error -> {:error, {:computed_macro_error, meta, {:host_exception, error.__struct__}}}
  end

  defp resolve_field_types(field_types, env) when is_map(field_types) do
    Map.new(field_types, fn
      {field, {:record, name, fields}} ->
        repeated =
          fields
          |> Enum.filter(&(MacroFamily.field_cardinality(&1) in [:repeated, :one_or_more]))
          |> Enum.map(& &1.name)

        {field,
         {:record, Cure.Core.Env.resolve_key(env, env.ctors, name),
          Enum.map(fields, &Map.put(&1, :repeated, &1.name in repeated))}}

      {field, value} ->
        {field, value}
    end)
  end

  defp resolve_field_types(_field_types, _env), do: %{}

  defp primitive_field_types?(field_types) when is_map(field_types) do
    Enum.any?(field_types, fn {_field, type} -> match?({:primitive, _shape}, type) end)
  end

  defp primitive_field_types?(_field_types), do: false

  defp global_names({:global, name}), do: [name]
  defp global_names({:app, f, a}), do: global_names(f) ++ global_names(a)
  defp global_names({:lam, _grade, domain, body}), do: global_names(domain) ++ global_names(body)
  defp global_names({:pi, _grade, domain, codomain}), do: global_names(domain) ++ global_names(codomain)

  defp global_names({:case, scrutinee, motive, branches}) do
    global_names(scrutinee) ++
      global_names(motive) ++ Enum.flat_map(branches, fn {_name, _arity, body} -> global_names(body) end)
  end

  defp global_names({:let, _grade, type, value, body}),
    do: global_names(type) ++ global_names(value) ++ global_names(body)

  defp global_names({:effect_type, inner}), do: global_names(inner)
  defp global_names({:effect_pure, value}), do: global_names(value)

  defp global_names({:effect_bind, effect, continuation}),
    do: global_names(effect) ++ global_names(continuation)

  defp global_names({:ctor, _name, args}), do: Enum.flat_map(args, &global_names/1)
  defp global_names({:data, _name, params, indices}), do: Enum.flat_map(params ++ indices, &global_names/1)
  defp global_names(term) when is_list(term), do: Enum.flat_map(term, &global_names/1)

  defp global_names(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&global_names/1)

  defp global_names(_term), do: []

  defp direct_input_cores({:syn_node, _tag, _attrs, kids}, fields, field_types) do
    fields
    |> Enum.zip(kids)
    |> Enum.map(fn {field, kid} ->
      case Map.get(field_types, field) do
        {:record, nested_name, nested_fields} ->
          repeated =
            nested_fields
            |> Enum.filter(&(MacroFamily.field_cardinality(&1) in [:repeated, :one_or_more]))
            |> Enum.map(& &1.name)

          nested_field_types = MacroSyntax.family_field_types(nested_fields)

          MacroSyntax.to_core_record_without_context(
            nested_name,
            Enum.map(nested_fields, & &1.name),
            repeated,
            kid,
            nested_field_types
          )

        {:primitive, shape} ->
          MacroSyntax.to_core_primitive_value(kid, shape)

        _ ->
          MacroSyntax.to_core(kid)
      end
    end)
  end

  defp direct_input_cores(_input_repr, _fields, _field_types), do: []

  defp execute_application(context, elab_core, [candidate | fallback]) when is_list(candidate) do
    application = Enum.reduce(candidate, elab_core, fn input_core, function -> {:app, function, input_core} end)

    case Kernel.infer(context, application) do
      {:ok, _result_type} ->
        result = Normalise.nf(context, application, fuel: @normalise_fuel)

        case decode_result(result) do
          {:ok, _ast} = success ->
            success

          {:error, reason} when fallback != [] ->
            if fallback_decode_error?(reason),
              do: execute_application(context, elab_core, fallback),
              else: {:error, reason}

          error ->
            error
        end

      {:error, _reason} when fallback != [] ->
        execute_application(context, elab_core, fallback)

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp execute_application(_context, _elab_core, []),
    do: {:error, :no_compatible_macro_input}

  defp fallback_decode_error?({:author_failure, _name, _args}), do: false
  defp fallback_decode_error?({:author_diagnostics, _diagnostics}), do: false
  defp fallback_decode_error?({:invalid_generated_syntax, _reason}), do: false
  defp fallback_decode_error?(_reason), do: true

  defp decode_result(result) do
    if result == :fuel_exhausted do
      {:error, :normalization_fuel_exhausted}
    else
      decode_result_term(result)
    end
  end

  defp decode_result_term(result) do
    case MacroSyntax.from_core_macro_result(result) do
      {:expanded, repr} ->
        validate_expansion(repr)

      {:rejected, diagnostics} ->
        {:error, {:author_diagnostics, Enum.map(diagnostics, &MacroSyntax.from_syntax/1)}}

      {:error, reason} ->
        {:error, reason}

      :not_macro_result ->
        case MacroSyntax.from_core(result) do
          {:error, reason} ->
            {:error, reason}

          {:syn_failure, name, args} ->
            {:error, {:author_failure, Atom.to_string(name), Enum.map(args, &MacroSyntax.from_syntax/1)}}

          repr ->
            validate_expansion(repr)
        end
    end
  end

  defp validate_expansion(repr) do
    case MacroSyntax.validate_expansion(repr) do
      :ok -> {:ok, MacroSyntax.from_syntax(repr)}
      {:error, reason} -> {:error, {:invalid_generated_syntax, reason}}
    end
  end
end
