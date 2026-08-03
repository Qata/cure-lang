defmodule Cure.Compiler.ModulePipeline.Interface do
  @moduledoc false

  alias Cure.Compiler.ModuleInterface
  alias Cure.Core.{Builtins, Env, Kernel}

  @artifact_magic "CUREIFACE\0"
  @artifact_version 1
  @extension ".cureinterface"

  @spec path(Path.t(), String.t()) :: Path.t()
  def path(root, module_name) when is_binary(root) and is_binary(module_name),
    do: Path.join(root, module_name <> @extension)

  @spec write(ModuleInterface.t(), Path.t()) :: :ok | {:error, term()}
  def write(%ModuleInterface{} = interface, root) do
    with :ok <- ModuleInterface.validate(interface),
         :ok <- File.mkdir_p(root) do
      destination = path(root, interface.module_name)
      payload = :erlang.term_to_binary(interface, [:deterministic, compressed: 6])
      checksum = :crypto.hash(:sha256, payload)
      File.write(destination, [@artifact_magic, <<@artifact_version>>, checksum, payload], [:binary])
    end
  end

  @spec read(Path.t()) :: {:ok, ModuleInterface.t()} | {:error, term()}
  def read(path) when is_binary(path) do
    with {:ok, <<@artifact_magic, @artifact_version, checksum::binary-size(32), payload::binary>>} <- File.read(path),
         :ok <- verify_payload_checksum(checksum, payload),
         {:ok, interface} <- decode(payload),
         :ok <- ModuleInterface.validate(interface) do
      {:ok, interface}
    else
      {:ok, <<@artifact_magic, version, _::binary>>} ->
        {:error, {:interface_artifact_version_incompatible, version, @artifact_version}}

      {:ok, _} ->
        {:error, :interface_artifact_header_invalid}

      {:error, _} = error ->
        error
    end
  end

  @spec load_roots([Path.t()]) :: {:ok, %{String.t() => ModuleInterface.t()}} | {:error, term()}
  def load_roots(roots) when is_list(roots) do
    result =
      roots
      |> Enum.flat_map(&Path.wildcard(Path.join(&1, "*" <> @extension)))
      |> Enum.uniq()
      |> Enum.sort()
      |> Enum.reduce_while({:ok, %{}}, fn artifact, {:ok, interfaces} ->
        with {:ok, interface} <- read(artifact),
             :ok <- reject_duplicate_provider(interfaces, interface, artifact) do
          {:cont, {:ok, Map.put(interfaces, interface.module_name, interface)}}
        else
          {:error, reason} -> {:halt, {:error, {:invalid_interface_artifact, artifact, reason}}}
        end
      end)

    with {:ok, interfaces} <- result,
         {:ok, universe} <- environment(interfaces),
         :ok <- verify_all(interfaces, universe) do
      {:ok, interfaces}
    end
  end

  defp decode(payload) do
    try do
      # Canonical Core keys include user-authored atoms (for example
      # :"Package.Module#definition"). A clean consumer VM necessarily has not
      # interned those atoms yet, so `[:safe]` cannot decode a valid compiler
      # interface. The checksum, schema/semantic hash validation, and kernel
      # verification above and below make this a checked compiler artifact,
      # analogous to loading BEAM, rather than an untrusted wire format.
      case :erlang.binary_to_term(payload) do
        %ModuleInterface{} = interface -> {:ok, interface}
        other -> {:error, {:interface_artifact_payload_invalid, other}}
      end
    rescue
      ArgumentError -> {:error, :interface_artifact_payload_invalid}
    end
  end

  defp verify_payload_checksum(checksum, payload) do
    if :crypto.hash(:sha256, payload) == checksum,
      do: :ok,
      else: {:error, :interface_artifact_checksum_mismatch}
  end

  defp reject_duplicate_provider(interfaces, interface, artifact) do
    case Map.fetch(interfaces, interface.module_name) do
      :error ->
        :ok

      {:ok, existing} ->
        {:error, {:duplicate_interface_provider, interface.module_name, existing.source_path, artifact}}
    end
  end

  @spec from_checked_env(Env.t(), Cure.Compiler.ModuleManifest.Entry.t(), String.t(), map()) ::
          ModuleInterface.t()
  def from_checked_env(%Env{} = env, entry, package, dependency_hashes \\ %{}) do
    owner = entry.module_name
    declarations = owned_declarations(env, owner)

    ModuleInterface.new(%{
      module_name: owner,
      source_path: entry.source_path,
      source_hash: entry.source_hash,
      dependency_interface_hashes: dependency_hashes,
      dependency_names: entry.dependencies |> Enum.map(&elem(&1.target, 1)) |> Enum.uniq() |> Enum.sort(),
      direct_edges: Enum.map(entry.dependencies, &interface_edge/1),
      canonical_declarations: declarations,
      canonical_externs: owned_externs(declarations.defs),
      extension_payloads:
        env
        |> owned_extensions(owner)
        |> Map.put(:canonical_identity, {package, owner}),
      source_metadata: %{package: package},
      owned_env: nil,
      export_env: nil
    })
  end

  @spec to_env(ModuleInterface.t()) :: {:ok, Env.t()} | {:error, term()}
  def to_env(%ModuleInterface{} = interface) do
    with :ok <- ModuleInterface.validate(interface) do
      declarations = interface.canonical_declarations
      extensions = interface.extension_payloads
      empty = Env.empty()

      {:ok,
       %Env{
         empty
         | defs: Map.get(declarations, :defs, %{}),
           families: Map.get(declarations, :families, %{}),
           ctors: Map.get(declarations, :ctors, %{}),
           ctor_to_family: Map.get(declarations, :ctor_to_family, %{}),
           equations: Map.get(declarations, :equations, %{}),
           interfaces: Map.get(extensions, :interfaces, %{}),
           coherence: Map.get(extensions, :coherence),
           primitives: Map.get(extensions, :primitives, %{}),
           certified: MapSet.new(),
           module_owner: interface.module_name
       }}
    end
  end

  @spec verify(ModuleInterface.t(), Env.t()) :: :ok | {:error, term()}
  def verify(%ModuleInterface{} = interface, %Env{} = dependencies \\ Env.empty()) do
    with {:ok, interface_env} <- to_env(interface),
         seeded = Builtins.seed(Env.empty(), MapSet.new()),
         env = seeded |> merge_for_verification(dependencies) |> merge_for_verification(interface_env),
         :ok <- verify_families(env, interface),
         :ok <- verify_constructors(env, interface),
         :ok <- verify_definitions(env, interface) do
      :ok
    end
  end

  @spec environment(map()) :: {:ok, Env.t()} | {:error, term()}
  def environment(interfaces) when is_map(interfaces) do
    interfaces
    |> Map.values()
    |> Enum.uniq_by(&{&1.module_name, &1.interface_hash})
    |> Enum.reduce_while({:ok, Env.empty()}, fn interface, {:ok, env} ->
      case to_env(interface) do
        {:ok, next} -> {:cont, {:ok, merge_for_verification(env, next)}}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
  end

  @spec verify_all(map(), Env.t()) :: :ok | {:error, term()}
  def verify_all(interfaces, %Env{} = universe) when is_map(interfaces) do
    interfaces
    |> Map.values()
    |> Enum.uniq_by(&{&1.module_name, &1.interface_hash})
    |> Enum.reduce_while(:ok, fn interface, :ok ->
      case verify(interface, universe) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_checked_interface, interface.module_name, reason}}}
      end
    end)
  end

  defp merge_for_verification(%Env{} = base, %Env{} = interface) do
    %Env{
      base
      | defs: Map.merge(base.defs, interface.defs),
        families: Map.merge(base.families, interface.families),
        ctors: Map.merge(base.ctors, interface.ctors),
        ctor_to_family: Map.merge(base.ctor_to_family, interface.ctor_to_family),
        interfaces: Map.merge(base.interfaces, interface.interfaces),
        primitives: Map.merge(base.primitives, interface.primitives),
        coherence: interface.coherence
    }
  end

  defp owned_declarations(env, owner) do
    %{
      defs: env.defs |> take_owned(owner) |> Map.new(fn {key, definition} -> {key, opaque_definition(definition)} end),
      families: take_owned(env.families, owner),
      ctors: take_owned(env.ctors, owner),
      ctor_to_family: Map.filter(env.ctor_to_family, fn {key, _} -> Cure.Elab.Name.owner(key) == owner end),
      equations: %{}
    }
  end

  defp opaque_definition(%{body: {:extern, _}} = definition), do: definition
  defp opaque_definition(%{body: nil} = definition), do: definition
  defp opaque_definition(definition), do: Map.put(definition, :body, {:hole, "__interface_opaque__"})

  defp owned_externs(defs), do: Map.filter(defs, fn {_key, definition} -> match?({:extern, _}, definition.body) end)

  defp owned_extensions(env, owner) do
    %{
      interfaces:
        Map.filter(env.interfaces, fn {_name, descriptor} ->
          descriptor_owner(descriptor) == owner
        end),
      coherence: owned_coherence(env.coherence, owner),
      primitives: env.primitives
    }
  end

  defp descriptor_owner(%{family: family}), do: Cure.Elab.Name.owner(family)
  defp descriptor_owner(_), do: nil

  defp owned_coherence(nil, _owner), do: nil

  defp owned_coherence(coherence, owner) do
    anon = Map.filter(coherence.anon, fn {_key, ref} -> reference_owner(ref) == owner end)
    named = Map.filter(coherence.named, fn {_key, ref} -> reference_owner(ref) == owner end)

    %{
      coherence
      | anon: anon,
        named: named,
        anon_origins: Map.take(coherence.anon_origins, Map.keys(anon)),
        named_origins: Map.take(coherence.named_origins, Map.keys(named))
    }
  end

  defp reference_owner(%{methods: methods}) when map_size(methods) > 0 do
    methods |> Map.values() |> List.first() |> Cure.Elab.Name.owner()
  end

  defp reference_owner(_), do: nil

  defp take_owned(table, owner), do: Map.filter(table, fn {key, _} -> Cure.Elab.Name.owner(key) == owner end)

  defp interface_edge(dependency) do
    %{
      kind: dependency.kind,
      target: elem(dependency.target, 1),
      line: dependency.span.line
    }
  end

  defp verify_families(env, interface) do
    interface.canonical_declarations
    |> Map.get(:families, %{})
    |> Map.keys()
    |> Enum.sort()
    |> Enum.reduce_while(:ok, fn family, :ok ->
      case Kernel.check_family(env, Map.fetch!(env.families, family)) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_interface_family, family, reason}}}
      end
    end)
  end

  defp verify_constructors(env, interface) do
    interface.canonical_declarations
    |> Map.get(:ctors, %{})
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.reduce_while(:ok, fn {constructor_name, constructor}, :ok ->
      with {:ok, family_name} <- Map.fetch(env.ctor_to_family, constructor_name),
           {:ok, family} <- Map.fetch(env.families, family_name),
           :ok <- Kernel.check_ctor(env, family, constructor) do
        {:cont, :ok}
      else
        :error ->
          {:halt, {:error, {:invalid_interface_constructor_owner, constructor_name}}}

        {:error, reason} ->
          {:halt, {:error, {:invalid_interface_constructor, constructor_name, reason}}}
      end
    end)
  end

  defp verify_definitions(env, interface) do
    interface.canonical_declarations
    |> Map.get(:defs, %{})
    |> Map.keys()
    |> Enum.sort()
    |> Enum.reduce_while(:ok, fn definition, :ok ->
      case Kernel.check_def_type(env, definition) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_interface_definition, definition, reason}}}
      end
    end)
  end
end
