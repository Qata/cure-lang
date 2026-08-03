defmodule Cure.Compiler.ModuleManifest.Entry do
  @moduledoc false

  @enforce_keys [:identity, :module_name, :source_path, :source_hash]
  defstruct identity: nil,
            module_name: nil,
            source_path: nil,
            source_hash: nil,
            dependencies: [],
            prelude_provider?: false

  @type t :: %__MODULE__{}
end

defmodule Cure.Compiler.ModuleManifest do
  @moduledoc """
  Immutable canonical identity and bootstrap-dependency manifest for one
  compilation universe.

  This is the sole stored authority for mapping package/module identities to
  providers. It harvests declaration headers without elaborating bodies.
  """

  alias Cure.Compiler.ModuleManifest.Entry
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityScan}

  @enforce_keys [:package]
  defstruct package: nil, entries: %{}, paths: %{}, dependencies: %{}

  @type identity :: {String.t(), String.t()}
  @type dependency :: %{
          required(:kind) => :use_import | :qualified_reference,
          required(:source) => identity(),
          required(:target) => identity(),
          required(:span) => map()
        }

  @type t :: %__MODULE__{
          package: String.t(),
          entries: %{identity() => Entry.t()},
          paths: %{Path.t() => identity()},
          dependencies: %{identity() => [dependency()]}
        }

  @spec build([Path.t()], keyword()) :: {:ok, t()} | {:error, term()}
  def build(paths, opts \\ []) when is_list(paths) and is_list(opts) do
    package = Keyword.get(opts, :package, "root")
    paths = paths |> Enum.map(&Path.expand/1) |> Enum.uniq() |> Enum.sort()

    with :ok <- validate_package(package),
         {:ok, entries} <- scan_entries(paths, package),
         :ok <- reject_duplicates(entries),
         manifest = assemble(package, entries),
         :ok <- validate_dependencies(manifest, opts) do
      {:ok, manifest}
    end
  end

  @spec module_names(t()) :: [String.t()]
  def module_names(%__MODULE__{entries: entries}) do
    entries |> Map.keys() |> Enum.map(&elem(&1, 1)) |> Enum.sort()
  end

  @spec fetch(t(), String.t() | identity()) :: {:ok, Entry.t()} | {:error, term()}
  def fetch(%__MODULE__{package: package} = manifest, module_name) when is_binary(module_name),
    do: fetch(manifest, {package, module_name})

  def fetch(%__MODULE__{entries: entries}, identity) when is_tuple(identity) do
    case Map.fetch(entries, identity) do
      {:ok, entry} -> {:ok, entry}
      :error -> {:error, {:module_unavailable, identity}}
    end
  end

  @spec dependencies(t(), String.t() | identity()) :: [dependency()]
  def dependencies(%__MODULE__{package: package} = manifest, module_name) when is_binary(module_name),
    do: dependencies(manifest, {package, module_name})

  def dependencies(%__MODULE__{dependencies: dependencies}, identity),
    do: Map.get(dependencies, identity, [])

  @spec semantic_dump(t()) :: term()
  def semantic_dump(%__MODULE__{} = manifest) do
    manifest.entries
    |> Map.values()
    |> Enum.sort_by(& &1.identity)
    |> Enum.map(fn entry ->
      %{
        identity: entry.identity,
        source_path: entry.source_path,
        source_hash: entry.source_hash,
        prelude_provider?: entry.prelude_provider?,
        dependencies:
          Enum.map(entry.dependencies, fn dependency ->
            Map.take(dependency, [:kind, :source, :target, :span])
          end)
      }
    end)
  end

  defp validate_package(package) when is_binary(package) and package != "", do: :ok
  defp validate_package(package), do: {:error, {:invalid_package_identity, package}}

  defp scan_entries(paths, package) do
    Enum.reduce_while(paths, {:ok, []}, fn path, {:ok, entries} ->
      case scan_entry(path, package) do
        {:ok, entry} -> {:cont, {:ok, [entry | entries]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp scan_entry(path, package) do
    with {:ok, source} <- File.read(path) do
      facts = FixityScan.harvest_source(source, path, BuiltinFixity.table())

      case facts.module do
        module_name when is_binary(module_name) ->
          identity = {package, module_name}

          dependencies =
            Enum.map(facts.uses, &dependency(:use_import, identity, package, path, &1)) ++
              Enum.map(
                facts.qualified_targets,
                &dependency(:qualified_reference, identity, package, path, &1)
              )

          {:ok,
           %Entry{
             identity: identity,
             module_name: module_name,
             source_path: path,
             source_hash: :crypto.hash(:sha256, source),
             dependencies: normalize_dependencies(dependencies),
             prelude_provider?: facts.prelude?
           }}

        _ ->
          {:error, {:module_identity_missing, path}}
      end
    else
      {:error, reason} -> {:error, {:module_manifest_source_error, path, reason}}
    end
  end

  defp dependency(kind, source, package, path, reference) do
    %{
      kind: kind,
      source: source,
      target: {package, reference.target},
      span: %{path: path, line: reference.line}
    }
  end

  defp normalize_dependencies(dependencies) do
    dependencies
    |> Enum.uniq_by(&{&1.kind, &1.target, &1.span.line})
    |> Enum.sort_by(&{&1.target, &1.kind, &1.span.line})
  end

  defp reject_duplicates(entries) do
    entries
    |> Enum.group_by(& &1.identity)
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.find_value(:ok, fn
      {_identity, [_entry]} ->
        nil

      {identity, duplicates} ->
        providers = duplicates |> Enum.map(& &1.source_path) |> Enum.sort()
        {:error, {:duplicate_module_identity, %{identity: identity, providers: providers}}}
    end)
  end

  defp assemble(package, entries) do
    entries = Map.new(entries, &{&1.identity, &1})

    %__MODULE__{
      package: package,
      entries: entries,
      paths: Map.new(entries, fn {identity, entry} -> {entry.source_path, identity} end),
      dependencies: Map.new(entries, fn {identity, entry} -> {identity, entry.dependencies} end)
    }
  end

  defp validate_dependencies(manifest, opts) do
    known =
      opts
      |> Keyword.get(:known_modules, [])
      |> Enum.map(fn
        {_package, _module} = identity -> identity
        module when is_binary(module) -> {manifest.package, module}
      end)
      |> MapSet.new()
      |> MapSet.union(MapSet.new(Map.keys(manifest.entries)))

    missing =
      manifest.entries
      |> Map.keys()
      |> Enum.sort()
      |> Enum.find_value(fn identity ->
        manifest
        |> dependencies(identity)
        |> Enum.find(&(not MapSet.member?(known, &1.target)))
      end)

    if missing do
      {:error,
       {:missing_module,
        %{
          requester: missing.source,
          target: missing.target,
          kind: missing.kind,
          span: missing.span
        }}}
    else
      :ok
    end
  end
end
