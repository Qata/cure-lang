defmodule Cure.Elab.Program do
  @moduledoc """
  Whole-program elaboration (design spec §5, M9.2 wiring): lex + parse a source
  string, elaborate every declaration into the `Cure.Core` signature, then run
  the type-level totality closure so that any function reduced by the type
  checker is kernel-certified total (§7). Returns the fully-elaborated,
  totality-certified signature.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.{Declarations, Erase, TotalityClosure}
  alias Cure.Stdlib.Paths

  @spec elaborate(String.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate(source) when is_binary(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      check_ast(ast)
    end
  end

  @doc """
  Elaborate + totality-certify an already-parsed module/declaration AST. Unwraps
  a `mod ... end` container to its body. This is the entry the real compiler's
  type checker calls for dependent modules.
  """
  @spec check_ast(tuple() | list()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast(ast) do
    with {:ok, env0} <- import_env(imports(ast), MapSet.new()),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0) do
      TotalityClosure.certify_type_level(env)
    end
  end

  @doc """
  Elaborate a module and return the definitions declared directly by that
  module. Imported stdlib definitions remain in the env for type checking and
  conversion, but codegen should emit only `local_defs`.
  """
  @spec check_ast_with_locals(tuple() | list()) :: {:ok, Env.t(), [atom()]} | {:error, term()}
  def check_ast_with_locals(ast) do
    local_defs = local_def_names(ast)

    with {:ok, env} <- check_ast(ast) do
      {:ok, env, local_defs}
    end
  end

  @doc """
  Does a parsed program/AST use dependent constructs the kernel must check?
  Currently keyed on the presence of an `indexed type` (GADT) declaration.
  """
  @spec dependent?(term()) :: boolean()
  def dependent?({:indexed_type, _meta, _body}), do: true

  def dependent?({_tag, _meta, children}) when is_list(children),
    do: Enum.any?(children, &dependent?/1)

  def dependent?(list) when is_list(list), do: Enum.any?(list, &dependent?/1)
  def dependent?(_other), do: false

  @doc """
  Extract the `Cure.<Name>` module atom from a parsed `mod … end` program,
  defaulting to `Cure.Main` when no module container is present.
  """
  @spec module_atom(term()) :: module()
  def module_atom(ast), do: String.to_atom("Cure." <> (find_module_name(ast) || "Main"))

  defp find_module_name({:container, meta, _body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module, do: Keyword.get(meta, :name)
  end

  defp find_module_name({_tag, _meta, children}) when is_list(children),
    do: Enum.find_value(children, &find_module_name/1)

  defp find_module_name(list) when is_list(list), do: Enum.find_value(list, &find_module_name/1)
  defp find_module_name(_other), do: nil

  @doc """
  Hole goal reports (design spec §10/§11): for every definition whose body still
  carries a hole, report the hole's **goal type** (the definition's return type)
  and its **local context** (the parameter types in scope). This is the
  `:hole_goal` diagnostic — a hole typechecks, reports what must fill it, and
  blocks codegen until filled.
  """
  @spec hole_goals(Env.t()) :: [%{function: atom(), goal: term(), context: [term()]}]
  def hole_goals(%Env{defs: defs}) do
    for {name, %{type: type, body: body}} <- defs, Erase.has_hole?(body) do
      {context, goal} = split_pi(type, [])
      %{function: name, goal: goal, context: context}
    end
  end

  defp split_pi({:pi, dom, cod}, acc), do: split_pi(cod, [dom | acc])
  defp split_pi(goal, acc), do: {Enum.reverse(acc), goal}

  @doc """
  Codegen gate (§6 negative #5): a program with an unfilled hole typechecks but
  must not be emitted. Returns `{:error, {:unfilled_hole, name}}` for the first
  definition that still carries a hole.
  """
  @spec check_codegen_ready(Env.t()) :: :ok | {:error, {:unfilled_hole, atom()}}
  def check_codegen_ready(%Env{defs: defs}) do
    case Enum.find(defs, fn {_name, %{body: body}} -> Erase.has_hole?(body) end) do
      nil -> :ok
      {name, _def} -> {:error, {:unfilled_hole, name}}
    end
  end

  # Flatten a parsed program into a flat list of top-level declarations,
  # unwrapping `{:block, …}` groupings and `mod … end` module containers while
  # leaving ADT/GADT/function declarations intact. Stray sibling nodes the parser
  # can place next to a module container (e.g. a bare `{:variable, …}`) are
  # dropped, mirroring how codegen locates the container and ignores siblings.
  defp declarations({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &declarations/1)

  defp declarations({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module do
      body |> List.wrap() |> Enum.flat_map(&declarations/1)
    else
      [{:container, meta, body}]
    end
  end

  defp declarations({:function_def, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :name) == "__group__", do: [], else: [{:function_def, meta, body}]
  end

  defp declarations({tag, _meta, _body} = node) when tag in [:container, :indexed_type], do: [node]
  defp declarations(_other), do: []

  defp local_def_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(fn
      {:function_def, meta, _body} ->
        case Keyword.get(meta, :name) do
          "__group__" -> []
          name when is_binary(name) -> [String.to_atom(name)]
          _ -> []
        end

      _ ->
        []
    end)
  end

  defp imports({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &imports/1)

  defp imports({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module do
      body |> List.wrap() |> Enum.flat_map(&imports/1)
    else
      []
    end
  end

  defp imports({:import, meta, _}) when is_list(meta), do: [Keyword.fetch!(meta, :source)]

  defp imports({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &imports/1)

  defp imports(list) when is_list(list), do: Enum.flat_map(list, &imports/1)
  defp imports(_other), do: []

  defp import_env([], _seen), do: {:ok, Env.empty()}

  defp import_env(imports, seen) do
    Enum.reduce_while(imports, {:ok, Env.empty()}, fn source, {:ok, acc} ->
      case source |> import_source_path() |> import_source_env(seen) do
        {:ok, imported} -> {:cont, {:ok, merge_env(acc, imported)}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp import_source_env(:not_stdlib, _seen), do: {:ok, Env.empty()}

  defp import_source_env({:ok, module_name, path}, seen) do
    if MapSet.member?(seen, module_name) do
      {:ok, Env.empty()}
    else
      with {:ok, source} <- File.read(path),
           {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
           {:ok, ast} <- Parser.parse(tokens, emit_events: false),
           {:ok, env0} <- import_env(imports(ast), MapSet.put(seen, module_name)),
           {:ok, env} <- elaborate_declarations(declarations(ast), env0) do
        TotalityClosure.certify_type_level(env)
      else
        {:error, reason} -> {:error, {:dependent_import_failed, module_name, reason}}
      end
    end
  end

  defp import_source_path(source) do
    case String.split(source, ".") do
      ["Std", name] ->
        case Paths.source_dir() do
          nil ->
            {:error, {:missing_stdlib_source_dir, source}}

          dir ->
            path = Path.join(dir, String.downcase(name) <> ".cure")

            if File.exists?(path) do
              {:ok, source, path}
            else
              {:error, {:missing_stdlib_source, source, path}}
            end
        end

      _ ->
        :not_stdlib
    end
  end

  defp merge_env(%Env{} = left, %Env{} = right) do
    %Env{
      families: Map.merge(left.families, right.families),
      ctors: Map.merge(left.ctors, right.ctors),
      ctor_to_family: Map.merge(left.ctor_to_family, right.ctor_to_family),
      defs: Map.merge(left.defs, right.defs),
      certified: MapSet.union(left.certified || MapSet.new(), right.certified || MapSet.new())
    }
  end

  defp elaborate_declarations(items, env) do
    Enum.reduce_while(items, {:ok, env}, fn decl, {:ok, acc} ->
      case Declarations.elaborate(decl, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
