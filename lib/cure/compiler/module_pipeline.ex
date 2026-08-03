defmodule Cure.Compiler.ModulePipeline do
  @moduledoc """
  Canonical module compilation boundary.

  The implementation is deliberately phase-oriented: discovery creates the
  immutable manifest, header collection creates skeletons, and later phases
  add checked interfaces, bodies, closure, and artifacts to the same result.
  """

  alias Cure.Compiler.{Lexer, ModuleManifest, ModuleSkeleton, Parser}
  alias Cure.Compiler.ModulePipeline.{Request, Result}

  @spec check([Path.t()], keyword()) :: {:ok, Result.t()} | {:error, term()}
  def check(paths, opts \\ []) when is_list(paths) and is_list(opts) do
    request_opts =
      opts
      |> Keyword.put_new(:entry_point, :module_check)
      |> Keyword.put(:sources, paths)

    with {:ok, request} <- Request.new(request_opts),
         :ok <- require_canonical(request),
         {:ok, manifest} <- ModuleManifest.build(paths, manifest_options(request)),
         {:ok, skeletons} <- collect_skeletons(manifest) do
      {:ok, %Result{request: request, manifest: manifest, skeletons: skeletons}}
    end
  end

  @spec resolve(Result.t(), String.t(), atom(), String.t()) :: {:ok, tuple()} | {:error, term()}
  def resolve(%Result{} = result, requesting_module, namespace, written_name)
      when is_binary(requesting_module) and is_atom(namespace) and is_binary(written_name) do
    if String.contains?(written_name, ".") do
      resolve_qualified(result, namespace, written_name)
    else
      resolve_bare(result, requesting_module, namespace, written_name)
    end
  end

  defp require_canonical(%Request{selection: :canonical}), do: :ok
  defp require_canonical(%Request{selection: selection}), do: {:error, {:module_pipeline_not_selected, selection}}

  defp manifest_options(request) do
    [package: request.package || "root", source_roots: request.source_roots]
  end

  defp collect_skeletons(manifest) do
    manifest.entries
    |> Map.values()
    |> Enum.sort_by(& &1.identity)
    |> Enum.reduce_while({:ok, %{}}, fn entry, {:ok, skeletons} ->
      with {:ok, source} <- File.read(entry.source_path),
           {:ok, tokens} <- Lexer.tokenize(source, file: entry.source_path, emit_events: false),
           {:ok, ast} <- Parser.parse(tokens, file: entry.source_path, emit_events: false) do
        skeleton = ModuleSkeleton.collect(ast, entry.identity, entry.source_path)
        {:cont, {:ok, Map.put(skeletons, entry.identity, skeleton)}}
      else
        {:error, reason} -> {:halt, {:error, {:module_skeleton_error, entry.identity, reason}}}
      end
    end)
  end

  defp resolve_qualified(result, namespace, written_name) do
    parts = String.split(written_name, ".")
    declaration_name = List.last(parts)
    module_name = parts |> Enum.drop(-1) |> Enum.join(".")

    with {:ok, skeleton} <- fetch_skeleton(result, module_name),
         {:ok, declaration} <- fetch_declaration(skeleton, namespace, declaration_name),
         :ok <- require_public(declaration) do
      {:ok, declaration.key}
    end
  end

  defp resolve_bare(result, requesting_module, namespace, name) do
    with {:ok, requester} <- fetch_skeleton(result, requesting_module) do
      case Map.fetch(requester.declarations, {namespace, name}) do
        {:ok, declaration} ->
          {:ok, declaration.key}

        :error ->
          result.manifest
          |> ModuleManifest.dependencies(requesting_module)
          |> Enum.filter(&(&1.kind == :use_import))
          |> Enum.reduce([], fn dependency, candidates ->
            case Map.fetch(result.skeletons, dependency.target) do
              {:ok, skeleton} ->
                case Map.fetch(skeleton.declarations, {namespace, name}) do
                  {:ok, %{visibility: :public} = declaration} -> [declaration | candidates]
                  _ -> candidates
                end

              :error ->
                candidates
            end
          end)
          |> resolve_candidates(name)
      end
    end
  end

  defp resolve_candidates([], _name), do: {:error, :not_in_lexical_scope}
  defp resolve_candidates([declaration], _name), do: {:ok, declaration.key}

  defp resolve_candidates(declarations, name) do
    {:error, {:ambiguous_name, name, declarations |> Enum.map(& &1.key) |> Enum.sort()}}
  end

  defp fetch_skeleton(%Result{request: request, skeletons: skeletons}, module_name) do
    identity = {request.package || "root", module_name}

    case Map.fetch(skeletons, identity) do
      {:ok, skeleton} -> {:ok, skeleton}
      :error -> {:error, {:module_unavailable, identity}}
    end
  end

  defp fetch_declaration(skeleton, namespace, name) do
    case Map.fetch(skeleton.declarations, {namespace, name}) do
      {:ok, declaration} -> {:ok, declaration}
      :error -> {:error, {:declaration_unavailable, skeleton.identity, namespace, name}}
    end
  end

  defp require_public(%{visibility: :public}), do: :ok
  defp require_public(%{visibility: :private}), do: {:error, :private_declaration}
end
