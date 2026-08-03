defmodule Cure.Compiler.ModulePipeline do
  @moduledoc """
  Canonical module compilation boundary.

  The implementation is deliberately phase-oriented: discovery creates the
  immutable manifest, header collection creates skeletons, and later phases
  add checked interfaces, bodies, closure, and artifacts to the same result.
  """

  alias Cure.Compiler.{Lexer, ModuleManifest, ModuleSkeleton, Parser}
  alias Cure.Compiler.ModulePipeline.{Interface, Request, Result}
  alias Cure.Core.Env
  alias Cure.Elab.Program

  @spec check([Path.t()], keyword()) :: {:ok, Result.t()} | {:error, term()}
  def check(paths, opts \\ []) when is_list(paths) and is_list(opts) do
    request_opts =
      opts
      |> Keyword.put_new(:entry_point, :module_check)
      |> Keyword.put(:sources, paths)

    with {:ok, request} <- Request.new(request_opts),
         :ok <- require_canonical(request),
         {:ok, external_interfaces} <- Interface.load_roots(request.interface_roots),
         {:ok, external_envs} <- interface_environments(external_interfaces),
         {:ok, manifest} <-
           ModuleManifest.build(paths, manifest_options(request, external_interfaces)),
         {:ok, skeletons, asts, sources} <- collect_units(manifest),
         {:ok, interfaces, checked_envs} <-
           check_modules(manifest, asts, sources, external_interfaces, external_envs) do
      {:ok,
       %Result{
         request: request,
         manifest: manifest,
         skeletons: skeletons,
         asts: asts,
         interfaces: interfaces,
         checked_envs: checked_envs
       }}
    end
  end

  @spec write_interfaces(Result.t(), Path.t()) :: :ok | {:error, term()}
  def write_interfaces(%Result{} = result, root) when is_binary(root) do
    result.interfaces
    |> Map.values()
    |> Enum.uniq_by(&{&1.module_name, &1.interface_hash})
    |> Enum.sort_by(& &1.module_name)
    |> Enum.reduce_while(:ok, fn interface, :ok ->
      case Interface.write(interface, root) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:interface_write_failed, interface.module_name, reason}}}
      end
    end)
  end

  @spec interface_path(Path.t(), String.t()) :: {:ok, Path.t()} | {:error, term()}
  def interface_path(root, module_name) when is_binary(root) and is_binary(module_name) do
    path = Interface.path(root, module_name)
    if File.regular?(path), do: {:ok, path}, else: {:error, {:interface_artifact_missing, module_name, path}}
  end

  @spec kernel_verify_interfaces(Result.t()) :: :ok | {:error, term()}
  def kernel_verify_interfaces(%Result{} = result) do
    result.interfaces
    |> Map.values()
    |> Enum.uniq_by(&{&1.module_name, &1.interface_hash})
    |> Enum.reduce_while(:ok, fn interface, :ok ->
      case Interface.verify(interface) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_checked_interface, interface.module_name, reason}}}
      end
    end)
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

  defp manifest_options(request, external_interfaces) do
    [
      package: request.package || "root",
      source_roots: request.source_roots,
      known_modules: Map.keys(external_interfaces)
    ]
  end

  defp collect_units(manifest) do
    manifest.entries
    |> Map.values()
    |> Enum.sort_by(& &1.identity)
    |> Enum.reduce_while({:ok, %{}, %{}, %{}}, fn entry, {:ok, skeletons, asts, sources} ->
      with {:ok, source} <- File.read(entry.source_path),
           {:ok, tokens} <- Lexer.tokenize(source, file: entry.source_path, emit_events: false),
           {:ok, ast} <- Parser.parse(tokens, file: entry.source_path, emit_events: false) do
        skeleton = ModuleSkeleton.collect(ast, entry.identity, entry.source_path)

        {:cont,
         {:ok, Map.put(skeletons, entry.identity, skeleton), Map.put(asts, entry.identity, ast),
          Map.put(sources, entry.identity, source)}}
      else
        {:error, reason} -> {:halt, {:error, {:module_skeleton_error, entry.identity, reason}}}
      end
    end)
  end

  defp check_modules(manifest, asts, sources, external_interfaces, external_envs) do
    manifest
    |> dependency_order()
    |> Enum.reduce_while(
      {:ok, external_interface_table(manifest, external_interfaces), external_env_table(manifest, external_envs)},
      fn identity, {:ok, interfaces, checked_envs} ->
        entry = Map.fetch!(manifest.entries, identity)

        with {:ok, imported} <- imported_environment(manifest, identity, checked_envs),
             {:ok, prepared} <-
               Program.canonical_register_interface(Map.fetch!(asts, identity), imported,
                 module_name: entry.module_name,
                 source: Map.fetch!(sources, identity),
                 file: entry.source_path,
                 module_visibility: module_visibility(manifest, identity)
               ),
             {:ok, checked} <- Program.canonical_check_bodies(prepared),
             dependency_hashes = dependency_hashes(manifest, identity, interfaces),
             interface <- Interface.from_checked_env(checked, entry, manifest.package, dependency_hashes),
             :ok <- Interface.verify(interface),
             {:ok, interface_env} <- Interface.to_env(interface) do
          {:cont, {:ok, Map.put(interfaces, identity, interface), Map.put(checked_envs, identity, interface_env)}}
        else
          {:error, reason} -> {:halt, {:error, {:module_check_failed, identity, reason}}}
        end
      end
    )
  end

  defp interface_environments(interfaces) do
    Enum.reduce_while(interfaces, {:ok, %{}}, fn {module_name, interface}, {:ok, envs} ->
      case Interface.to_env(interface) do
        {:ok, env} -> {:cont, {:ok, Map.put(envs, module_name, env)}}
        {:error, reason} -> {:halt, {:error, {:invalid_interface_environment, module_name, reason}}}
      end
    end)
  end

  defp external_interface_table(manifest, interfaces),
    do: Map.new(interfaces, fn {module_name, interface} -> {{manifest.package, module_name}, interface} end)

  defp external_env_table(manifest, envs),
    do: Map.new(envs, fn {module_name, env} -> {{manifest.package, module_name}, env} end)

  defp module_visibility(manifest, identity) do
    dependencies = ModuleManifest.dependencies(manifest, identity)

    lexical =
      dependencies
      |> Enum.filter(&(&1.kind == :use_import))
      |> MapSet.new(&elem(&1.target, 1))

    qualified =
      dependencies
      |> MapSet.new(&elem(&1.target, 1))

    %{lexical: lexical, qualified: qualified}
  end

  defp dependency_order(manifest) do
    identities = manifest.entries |> Map.keys() |> Enum.sort()
    {_visited, order} = Enum.reduce(identities, {MapSet.new(), []}, &visit_dependency(&1, manifest, &2))
    Enum.reverse(order)
  end

  defp visit_dependency(identity, manifest, {visited, order}) do
    if MapSet.member?(visited, identity) do
      {visited, order}
    else
      visited = MapSet.put(visited, identity)

      {visited, order} =
        manifest
        |> ModuleManifest.dependencies(identity)
        |> Enum.map(& &1.target)
        |> Enum.filter(&Map.has_key?(manifest.entries, &1))
        |> Enum.sort()
        |> Enum.reduce({visited, order}, &visit_dependency(&1, manifest, &2))

      {visited, [identity | order]}
    end
  end

  defp imported_environment(manifest, identity, checked_envs) do
    manifest
    |> ModuleManifest.dependencies(identity)
    |> Enum.map(& &1.target)
    |> Enum.uniq()
    |> Enum.sort()
    |> Enum.reduce_while({:ok, Env.empty()}, fn dependency, {:ok, imported} ->
      case Map.fetch(checked_envs, dependency) do
        {:ok, dependency_env} ->
          case Program.merge_canonical_environments(imported, dependency_env) do
            {:ok, merged} -> {:cont, {:ok, merged}}
            {:error, reason} -> {:halt, {:error, reason}}
          end

        :error ->
          {:halt, {:error, {:interface_dependency_unavailable, identity, dependency}}}
      end
    end)
  end

  defp dependency_hashes(manifest, identity, interfaces) do
    manifest
    |> ModuleManifest.dependencies(identity)
    |> Enum.map(& &1.target)
    |> Enum.uniq()
    |> Map.new(fn dependency ->
      interface = Map.fetch!(interfaces, dependency)
      {elem(dependency, 1), interface.interface_hash}
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
