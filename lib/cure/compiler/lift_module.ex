defmodule Cure.Compiler.LiftModule do
  @moduledoc """
  Generic collection and emission of parsed `lift module` declarations.

  A lifted module is a quoted compilation unit, not an OTP-specific compiler
  object. Callback bodies become ordinary Cure function declarations and pass
  through the same dependent elaborator and emitter as the enclosing module.
  """

  alias Cure.Compiler.OtpMacro
  alias Cure.Elab.{Emit, Program}

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

  @spec strip(term()) :: term()
  def strip({:container, meta, body}) when is_list(meta) and is_list(body) do
    {:container, meta, Enum.reject(body, &match?({:lift_module, _, _}, &1))}
  end

  def strip(ast), do: ast

  @spec emit(map()) :: {:ok, unit()} | {:error, term()}
  def emit(%{module: module, behaviour: behaviour} = request) do
    with {:ok, module_ast} <- ordinary_module_ast(request),
         {:ok, env, local_defs} <- Program.check_ast_with_locals(module_ast),
         {:ok, forms} <- Emit.compile_forms(env, Program.module_atom(module_ast), local_defs) do
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
    case OtpMacro.lift_module_ast({:lift_module, meta, []}) do
      {:ok, request} -> {:ok, [request | acc]}
      {:error, reason} -> {:error, reason}
    end
  end

  defp collect_node({:container, meta, body}, acc) when is_list(meta) and is_list(body) do
    Enum.reduce_while(body, {:ok, acc}, fn child, {:ok, acc} ->
      case child do
        {:lift_module, _, _} ->
          case collect_node(child, acc) do
            {:ok, acc} -> {:cont, {:ok, acc}}
            {:error, _} = error -> {:halt, error}
          end

        _ ->
          {:cont, {:ok, acc}}
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

  defp callback_definition(%{name: name, params: params, body: body, line: line})
       when is_atom(name) and is_list(params) and is_tuple(body) do
    {:ok,
     {:function_def,
      [
        name: Atom.to_string(name),
        params: params,
        return_type: nil,
        visibility: :public,
        arity: length(params),
        line: line,
        col: 1
      ], [body]}}
  end

  defp callback_definition(callback), do: {:error, {:invalid_lift_callback, callback}}

  defp add_behaviour_attribute(forms, behaviour) do
    {attrs, rest} = Enum.split_while(forms, &match?({:attribute, _, _, _}, &1))
    attrs ++ [{:attribute, 1, :behaviour, behaviour}] ++ rest
  end
end
