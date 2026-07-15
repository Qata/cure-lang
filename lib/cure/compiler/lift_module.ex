defmodule Cure.Compiler.LiftModule do
  @moduledoc """
  Generic collection and emission of parsed `lift module` declarations.

  A lifted module is a quoted compilation unit, not a behavior-specific compiler
  object. Callback bodies become ordinary Cure function declarations and pass
  through the same dependent elaborator and emitter as the enclosing module.
  """

  alias Cure.Compiler.MacroSyntax
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
    inherited = unit_declarations(strip(ast))

    with {:ok, requests} <- collect_node(ast, []),
         :ok <- reject_duplicate_modules(requests),
         requests = Enum.map(requests, &inherit_scope(&1, inherited)),
         {:ok, requests} <- order_requests(requests) do
      {:ok, requests}
    end
  end

  # A lifted module is generated INSIDE a compilation unit, so it sees that
  # unit's scope: its imports, its types, and its functions. Without this an
  # `actor` is sealed off from its own file — it can only speak in structural
  # types (`Atom`, `Tuple(Atom, Int)`) and can never name a type the program
  # declares, which is precisely what a derived message type would be.
  #
  # The lifted module's own definitions win: a template binds names of its own
  # (`State`, `Message`, `start_link`) that its callbacks are written against,
  # and an enclosing definition of the same name must not displace them.
  defp inherit_scope(request, inherited) do
    inherited =
      if Map.get(request, :inherit_imports, true) do
        inherited
      else
        Enum.reject(inherited, &match?({:import, _, _}, &1))
      end

    taken = taken_names(request)

    inherited =
      Enum.reject(inherited, fn node ->
        name = declared_name(node)
        name != nil and name in taken
      end)

    # Inherited declarations come FIRST: they lexically precede the lifted module
    # in the source, and the template's own declarations refer to them (a
    # `typealias Message = Tick` needs `Tick` already bound — unlike an inductive,
    # a type alias has no forward-reference pre-pass).
    declarations = inherited ++ request.declarations

    imports =
      if Map.get(request, :inherit_imports, true) do
        Enum.uniq(request.imports ++ imports_from_declarations(inherited))
      else
        request.imports
      end

    %{request | declarations: declarations, imports: imports, dependencies: imports}
  end

  defp taken_names(request) do
    callback_names = Enum.map(request.callbacks, &to_string(Map.get(&1, :name)))
    declared = request.declarations |> Enum.map(&declared_name/1) |> Enum.reject(&is_nil/1)

    MapSet.new(callback_names ++ declared)
  end

  # The declarations of the enclosing unit, unwrapping its module container the
  # way the elaborator's own declaration stream does.
  defp unit_declarations({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &unit_declarations/1)

  defp unit_declarations({:container, meta, body} = node) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module,
      do: body |> List.wrap() |> Enum.flat_map(&unit_declarations/1),
      else: [node]
  end

  # A computed macro's typed input record is synthesized by Program.declarations/1
  # from the macro definition rather than stored as a standalone parser node. A
  # lifted module inherits the same declaration stream, so reproduce that generic
  # record here; otherwise an inherited macro builder's `input.field` projection
  # is rechecked without the record family in the lifted environment.
  defp unit_declarations({:macro_def, meta, rules}) when is_list(meta) and is_list(rules) do
    rules
    |> Enum.filter(&(&1[:kind] == :computed))
    |> Enum.uniq_by(&Map.get(&1, :syntax_type))
    |> Enum.map(fn rule ->
      fields =
        rule
        |> Map.get(:syntax_fields, [])
        |> MacroSyntax.record_fields()
        |> Enum.map(fn field ->
          {:param, [type: macro_syntax_field_type(field, rule)], field}
        end)

      {:container,
       [
         container_type: :struct,
         name: Map.fetch!(rule, :syntax_type),
         macro_generated: true,
         line: Keyword.get(meta, :line, 0),
         col: Keyword.get(meta, :col, 0)
       ], fields}
    end)
  end

  defp unit_declarations({tag, meta, _} = node)
       when tag in [:import, :indexed_type, :function_def] and is_list(meta),
       do: [normalize_generated_declaration(node)]

  defp unit_declarations({:type_annotation, meta, _} = node) when is_list(meta) do
    if Keyword.has_key?(meta, :name) and not Keyword.get(meta, :refinement, false),
      do: [node],
      else: []
  end

  defp unit_declarations(_other), do: []

  defp normalize_generated_declaration({:function_def, meta, [body]}) do
    params = Keyword.get(meta, :params, [])

    if Enum.all?(params, &match?({:param, _, []}, &1)) do
      params = Enum.map(params, &normalize_generated_param/1)
      {:function_def, Keyword.put(meta, :params, params), [body]}
    else
      {:function_def, meta, [body]}
    end
  end

  defp normalize_generated_declaration(node), do: node

  defp normalize_generated_param({:param, meta, []}) do
    {:param, [type: Keyword.fetch!(meta, :type)], Keyword.fetch!(meta, :name)}
  end

  defp macro_syntax_field_type(field, rule) do
    if field in Map.get(rule, :syntax_repeated_fields, []) do
      {:function_call, [name: "List"], [{:variable, [scope: :local], "Syntax"}]}
    else
      {:variable, [scope: :local], "Syntax"}
    end
  end

  defp declared_name({:import, _meta, _children}), do: nil

  defp declared_name({tag, meta, _children})
       when tag in [:container, :indexed_type, :function_def, :type_annotation] and is_list(meta),
       do: Keyword.get(meta, :name)

  defp declared_name(_other), do: nil

  @doc "Validate and normalize a generic quoted module value."
  @spec request_ast(tuple()) :: {:ok, map()} | {:error, term()}
  def request_ast({:lift_module, meta, []}) when is_list(meta) do
    with {:ok, module} <- normalize_module_name(Keyword.get(meta, :module)),
         behaviour when is_atom(behaviour) <- Keyword.get(meta, :behaviour),
         callbacks when is_list(callbacks) <- Keyword.get(meta, :callbacks, []),
         declarations when is_list(declarations) <- Keyword.get(meta, :declarations, []),
         inherit_imports when is_boolean(inherit_imports) <- Keyword.get(meta, :inherit_imports, true),
         declarations = Enum.map(declarations, &normalize_generated_declaration/1),
         :ok <- validate_module_name(module),
         :ok <- validate_behaviour(behaviour),
         :ok <- validate_callbacks(callbacks),
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
         inherit_imports: inherit_imports,
         dependencies: imports,
         source_provenance: Keyword.get(meta, :source_provenance)
       }}
    else
      _ -> {:error, :invalid_lift_module_ast}
    end
  end

  def request_ast(_other), do: {:error, :invalid_lift_module_ast}

  # Computed macros reflect module names as syntax literals. Keep this
  # normalization generic: quoted source may use either the parser's existing
  # binary form or an atom produced by `Std.Syntax`, and neither form carries
  # behavior-specific meaning here.
  defp normalize_module_name(module) when is_binary(module), do: {:ok, module}
  defp normalize_module_name(module) when is_atom(module), do: {:ok, Atom.to_string(module)}

  defp normalize_module_name(module) when is_list(module) do
    if Enum.all?(module, &is_integer/1), do: {:ok, List.to_string(module)}, else: {:error, :invalid_lift_module_ast}
  end

  defp normalize_module_name(_module), do: {:error, :invalid_lift_module_ast}

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

  defp validate_callbacks(callbacks) do
    if Enum.all?(callbacks, &valid_callback?/1), do: :ok, else: {:error, :invalid_lift_callback}
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
