defmodule Cure.Elab.Resolution do
  @moduledoc """
  Surface-name resolution over canonical owner-qualified identities.

  Declaration identity is established by `Cure.Core.Env` and
  `Cure.Core.Inductive` while each module is elaborated. This module never
  rewrites Core terms or reconstructs binding identity after elaboration; it
  only maps a surface spelling to an already-registered canonical key.
  """

  alias Cure.Core.{Env, Inductive}

  @doc """
  Resolve a flattened dotted surface path to an already-canonical registry key.

  Qualified paths are exact. A missing qualified declaration is an error; the
  resolver deliberately does not fall back to a bare key, since doing so would
  make a qualified escape hatch depend on the importing environment.
  """
  @spec resolve_qualified(Env.t(), String.t(), :type | :value) :: {:ok, atom()} | :error
  def resolve_qualified(%Env{} = env, dotted, :value) do
    segs = String.split(dotted, ".")
    {mod_segs, [last]} = Enum.split(segs, length(segs) - 1)
    key = Cure.Elab.Name.qualify(Enum.join(mod_segs, "."), String.to_atom(last))
    try_keys(env, [key], :value)
  end

  def resolve_qualified(%Env{} = env, dotted, :type) do
    segs = String.split(dotted, ".")
    last = List.last(segs)
    {mod_segs, [explicit_last]} = Enum.split(segs, length(segs) - 1)

    candidates = [
      # Module==typename collapse: `Std.Nat` means `Std.Nat#Nat`.
      Cure.Elab.Name.qualify(dotted, String.to_atom(last)),
      # Explicit `Mod.Type` spelling.
      Cure.Elab.Name.qualify(Enum.join(mod_segs, "."), String.to_atom(explicit_last))
    ]

    try_keys(env, Enum.uniq(candidates), :type)
  end

  @doc """
  Resolve a bare spelling against canonical identities.

  The current module wins first. Otherwise an actual bare key is accepted for
  compatibility with ownerless synthetic environments. Finally, exactly one
  canonical suffix may resolve; multiple direct providers are ambiguous.
  """
  @spec resolve_bare(Env.t(), atom()) :: {:ok, atom()} | :none | {:ambiguous, [String.t()]}
  def resolve_bare(%Env{} = env, bare) do
    case local_or_bare_key(env, bare) do
      {:ok, key} -> {:ok, key}
      :none -> resolve_canonical_suffix(env, bare)
    end
  end

  defp local_or_bare_key(%Env{module_owner: owner} = env, bare) do
    candidates =
      if is_binary(owner),
        do: [Cure.Elab.Name.qualify(owner, bare), bare],
        else: [bare]

    case Enum.find(candidates, &present_in_any_namespace?(env, &1)) do
      nil -> :none
      key -> {:ok, key}
    end
  end

  defp resolve_canonical_suffix(env, bare) do
    suffix = "##{Atom.to_string(bare)}"

    matches =
      [env.ctors, env.families, env.defs]
      |> Enum.flat_map(&Map.keys/1)
      |> Enum.filter(fn key -> is_atom(key) and String.ends_with?(Atom.to_string(key), suffix) end)
      |> Enum.uniq()
      |> Enum.map(fn key -> {Cure.Elab.Name.owner(key), key} end)
      |> prefer_direct(env.import_modules)

    case matches do
      [{_owner, key}] -> {:ok, key}
      [] -> :none
      many -> {:ambiguous, Enum.map(many, &elem(&1, 0)) |> Enum.uniq()}
    end
  end

  defp present_in_any_namespace?(env, key) do
    Map.has_key?(env.families, key) or Map.has_key?(env.ctors, key) or Map.has_key?(env.defs, key)
  end

  # A direct import shadows a transitive re-export. If two direct providers
  # remain, the spelling is genuinely ambiguous.
  defp prefer_direct(matches, direct_modules) do
    case Enum.filter(matches, fn {owner, _key} -> MapSet.member?(direct_modules, owner) end) do
      [] -> matches
      directs -> directs
    end
  end

  @doc "Return the origin and canonical key of a shadowed bare spelling, if any."
  @spec shadowed_origin(Env.t(), atom()) :: {:ok, String.t(), atom()} | :error
  def shadowed_origin(%Env{} = env, bare) do
    case local_or_bare_key(env, bare) do
      {:ok, _key} ->
        :error

      :none ->
        suffix = "##{Atom.to_string(bare)}"

        Enum.find_value([env.ctors, env.families, env.defs], fn table ->
          Enum.find_value(Map.keys(table), fn key ->
            if is_atom(key) and String.ends_with?(Atom.to_string(key), suffix) do
              {:ok, Cure.Elab.Name.owner(key), key}
            end
          end)
        end) || :error
    end
  end

  @doc """
  Return all canonical providers of a bare spelling when no local or bare
  winner exists. This is used to produce the targeted ambiguity diagnostic.
  """
  @spec ambiguous_modules(Env.t(), atom()) :: [String.t()]
  def ambiguous_modules(%Env{} = env, bare) do
    case local_or_bare_key(env, bare) do
      {:ok, _key} ->
        []

      :none ->
        suffix = "##{Atom.to_string(bare)}"

        owners =
          [env.ctors, env.families, env.defs]
          |> Enum.flat_map(&Map.keys/1)
          |> Enum.filter(fn key -> is_atom(key) and String.ends_with?(Atom.to_string(key), suffix) end)
          |> Enum.map(&Cure.Elab.Name.owner/1)
          |> Enum.uniq()

        case Enum.filter(owners, &MapSet.member?(env.import_modules, &1)) do
          [] -> owners
          direct -> direct
        end
    end
  end

  defp try_keys(env, keys, slot) do
    present? =
      case slot do
        :type -> fn key -> Inductive.family?(env, key) or type_definition?(env, key) end
        :value -> fn key -> not is_nil(Inductive.get_ctor(env, key)) or Map.has_key?(env.defs, key) end
      end

    case Enum.find(keys, present?) do
      nil -> :error
      key -> {:ok, key}
    end
  end

  defp type_definition?(%Env{defs: defs}, key),
    do: match?(%{type: {:type, _level}}, Map.get(defs, key))
end
