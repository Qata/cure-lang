defmodule Cure.Compiler.LiftModule do
  @moduledoc """
  Generic collection and emission of parsed `lift module` declarations.

  A lifted module is a quoted compilation unit, not an OTP-specific compiler
  object. Callback bodies become ordinary Cure function declarations and pass
  through the same dependent elaborator and emitter as the enclosing module.
  """

  alias Cure.Elab.{Emit, Program}

  @callback_contracts %{
    gen_server: %{init: 1, handle_call: 3, handle_cast: 2, handle_info: 2, terminate: 2, code_change: 3},
    gen_statem: %{callback_mode: 0, init: 1, handle_event: 4},
    supervisor: %{init: 1},
    application: %{start: 2, stop: 1, start_phase: 3}
  }

  @type unit :: %{
          module: module(),
          forms: [tuple()],
          behaviour: atom(),
          dependencies: [String.t()],
          source_provenance: map() | nil
        }

  @spec collect(term()) :: {:ok, [map()]} | {:error, term()}
  def collect(ast) do
    with {:ok, requests} <- collect_node(ast, []),
         :ok <- reject_duplicate_modules(requests),
         {:ok, requests} <- order_requests(requests) do
      {:ok, requests}
    end
  end

  @doc "Validate and normalize a generic quoted module value."
  @spec request_ast(tuple()) :: {:ok, map()} | {:error, term()}
  def request_ast({:lift_module, meta, []}) when is_list(meta) do
    with module when is_binary(module) <- Keyword.get(meta, :module),
         behaviour when is_atom(behaviour) <- Keyword.get(meta, :behaviour),
         callbacks when is_list(callbacks) <- Keyword.get(meta, :callbacks, []),
         declarations when is_list(declarations) <- Keyword.get(meta, :declarations, []),
         :ok <- validate_module_name(module),
         :ok <- validate_behaviour(behaviour),
         :ok <- validate_callbacks(behaviour, callbacks),
         :ok <- validate_declarations(declarations),
         imports = Keyword.get(meta, :imports, imports_from_declarations(declarations)),
         :ok <- validate_imports(imports) do
      {:ok,
       %{
         kind: :quoted_module,
         module: module,
         behaviour: behaviour,
         callbacks: callbacks,
         declarations: declarations,
         imports: imports,
         dependencies: imports,
         source_provenance: Keyword.get(meta, :source_provenance)
       }}
    else
      {:error, _} = error -> error
      _ -> {:error, :invalid_lift_module_ast}
    end
  end

  def request_ast(_other), do: {:error, :invalid_lift_module_ast}

  @spec strip(term()) :: term()
  def strip({:lift_module, _meta, _children} = node), do: node

  def strip({tag, meta, children}) when is_list(children) do
    children =
      children
      |> Enum.map(&strip/1)
      |> Enum.reject(&match?({:lift_module, _, _}, &1))

    {tag, meta, children}
  end

  def strip(list) when is_list(list), do: Enum.map(list, &strip/1)
  def strip(ast), do: ast

  @spec emit(map()) :: {:ok, unit()} | {:error, term()}
  def emit(%{module: module, behaviour: behaviour} = request) do
    with {:ok, module_ast} <- ordinary_module_ast(request),
         {:ok, env, local_defs} <- Program.check_ast_with_locals(module_ast),
         origins = Program.import_origins(module_ast),
         {:ok, forms} <- Emit.compile_forms(env, Program.module_atom(module_ast), local_defs, origins) do
      {:ok,
       %{
         module: Program.module_atom(module_ast),
         forms: add_behaviour_attribute(forms, behaviour),
         behaviour: behaviour,
         dependencies: Map.get(request, :dependencies, []),
         source_provenance: Map.get(request, :source_provenance)
       }}
    else
      {:error, reason} -> {:error, {:lift_module_error, module, reason}}
    end
  end

  def emit(other), do: {:error, {:invalid_lift_module, other}}

  defp collect_node({:lift_module, meta, []}, acc) when is_list(meta) do
    case request_ast({:lift_module, meta, []}) do
      {:ok, request} -> {:ok, [request | acc]}
      {:error, reason} -> {:error, reason}
    end
  end

  defp collect_node({tag, _meta, children}, acc) when is_atom(tag) and is_list(children) do
    Enum.reduce_while(children, {:ok, acc}, fn child, {:ok, acc} ->
      case collect_node(child, acc) do
        {:ok, acc} -> {:cont, {:ok, acc}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> reverse_result()
  end

  defp collect_node(list, acc) when is_list(list) do
    Enum.reduce_while(list, {:ok, acc}, fn child, {:ok, acc} ->
      case collect_node(child, acc) do
        {:ok, acc} -> {:cont, {:ok, acc}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> reverse_result()
  end

  defp collect_node(_other, acc), do: {:ok, acc}

  defp reverse_result({:ok, requests}), do: {:ok, Enum.reverse(requests)}
  defp reverse_result(error), do: error

  defp reject_duplicate_modules(requests) do
    names = Enum.map(requests, &Map.get(&1, :module))

    case names -- Enum.uniq(names) do
      [] -> :ok
      [name | _] -> {:error, {:duplicate_lifted_module, name}}
    end
  end

  defp order_requests(requests) do
    by_name = Map.new(requests, &{&1.module, &1})
    names = Enum.map(requests, & &1.module)

    Enum.reduce_while(names, {:ok, [], MapSet.new(), MapSet.new()}, fn name, {:ok, ordered, visiting, visited} ->
      case visit(name, by_name, ordered, visiting, visited) do
        {:ok, ordered, visiting, visited} ->
          {:cont, {:ok, ordered, visiting, visited}}

        {:error, _} = error ->
          {:halt, error}
      end
    end)
    |> case do
      {:ok, ordered, _visiting, _visited} -> {:ok, ordered}
      {:error, _} = error -> error
    end
  end

  defp visit(name, by_name, ordered, visiting, visited) do
    cond do
      MapSet.member?(visited, name) ->
        {:ok, ordered, visiting, visited}

      MapSet.member?(visiting, name) ->
        {:error, {:lifted_module_dependency_cycle, name}}

      true ->
        request = Map.fetch!(by_name, name)
        visiting = MapSet.put(visiting, name)

        case Enum.reduce_while(Map.get(request, :dependencies, []), {:ok, ordered, visiting, visited}, fn dependency,
                                                                                                          {:ok, ordered,
                                                                                                           visiting,
                                                                                                           visited} =
                                                                                                            acc ->
               if Map.has_key?(by_name, dependency) do
                 case visit(dependency, by_name, ordered, visiting, visited) do
                   {:ok, _ordered, _visiting, _visited} = result -> {:cont, result}
                   {:error, _} = error -> {:halt, error}
                 end
               else
                 {:cont, acc}
               end
             end) do
          {:ok, ordered, visiting, visited} ->
            {:ok, ordered ++ [request], MapSet.delete(visiting, name), MapSet.put(visited, name)}

          {:error, _} = error ->
            error
        end
    end
  end

  defp ordinary_module_ast(%{module: module, callbacks: callbacks, declarations: declarations}) do
    with {:ok, module_name} <- ordinary_module_name(module),
         {:ok, callback_defs} <- callback_definitions(callbacks) do
      {:ok, {:container, [container_type: :module, name: module_name, language: :cure], callback_defs ++ declarations}}
    end
  end

  defp ordinary_module_name("Cure." <> name), do: {:ok, name}
  defp ordinary_module_name(name), do: {:error, {:invalid_lift_module_name, name}}

  defp callback_definitions(callbacks) do
    Enum.reduce_while(callbacks, {:ok, []}, fn callback, {:ok, acc} ->
      case callback_definition(callback) do
        {:ok, definition} -> {:cont, {:ok, [definition | acc]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, definitions} -> {:ok, Enum.reverse(definitions)}
      error -> error
    end
  end

  defp callback_definition(callback = %{name: name, params: params, return_type: return_type, body: body, line: line})
       when is_atom(name) and is_list(params) and is_tuple(body) do
    {:ok,
     {:function_def,
      [
        name: Atom.to_string(name),
        params: params,
        return_type: return_type,
        visibility: :public,
        arity: length(params),
        line: line,
        col: 1,
        callback_context: Map.get(callback, :callback_context)
      ], [body]}}
  end

  defp callback_definition(callback), do: {:error, {:invalid_lift_callback, callback}}

  defp add_behaviour_attribute(forms, behaviour) do
    {attrs, rest} = Enum.split_while(forms, &match?({:attribute, _, _, _}, &1))
    attrs ++ [{:attribute, 1, :behaviour, behaviour}] ++ rest
  end

  defp validate_module_name(name) do
    if Regex.match?(~r/^Cure\.[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*$/, name),
      do: :ok,
      else: {:error, {:invalid_module_name, name}}
  end

  defp validate_behaviour(behaviour) when is_atom(behaviour) and not is_nil(behaviour), do: :ok
  defp validate_behaviour(behaviour), do: {:error, {:invalid_behaviour, behaviour}}

  defp validate_callbacks(behaviour, callbacks) do
    with true <- Enum.all?(callbacks, &valid_callback?/1),
         :ok <- validate_known_callbacks(behaviour, callbacks) do
      :ok
    else
      false -> {:error, :invalid_lift_callback}
      {:error, _} = error -> error
    end
  end

  defp validate_known_callbacks(behaviour, callbacks) do
    case Map.get(@callback_contracts, normalize_behaviour(behaviour)) do
      nil ->
        :ok

      contract ->
        case Enum.find(callbacks, fn callback -> Map.get(contract, callback.name) != callback.arity end) do
          nil -> :ok
          %{name: name, arity: arity} -> {:error, {:invalid_lift_callback, normalize_behaviour(behaviour), name, arity}}
        end
    end
  end

  defp normalize_behaviour(behaviour) when is_atom(behaviour) do
    case behaviour do
      :GenServer -> :gen_server
      :GenStatem -> :gen_statem
      :Supervisor -> :supervisor
      :Application -> :application
      other -> other
    end
  end

  defp valid_callback?(%{name: name, arity: arity}) when is_atom(name) and is_integer(arity) and arity >= 0,
    do: true

  defp valid_callback?(_), do: false

  defp validate_declarations(declarations) do
    if Enum.all?(declarations, &is_tuple/1), do: :ok, else: {:error, :invalid_lift_declaration}
  end

  defp validate_imports(imports) do
    if Enum.all?(imports, &is_binary/1), do: :ok, else: {:error, :invalid_lift_import}
  end

  defp imports_from_declarations(declarations) do
    declarations
    |> Enum.flat_map(fn
      {:import, meta, _children} when is_list(meta) -> List.wrap(Keyword.get(meta, :source))
      _ -> []
    end)
    |> Enum.uniq()
  end
end
