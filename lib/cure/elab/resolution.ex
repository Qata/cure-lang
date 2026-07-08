defmodule Cure.Elab.Resolution do
  @moduledoc """
  E-layer resolution over the bare-atom registry (Approach B). Detects
  family-name collisions between imported modules and the local module, re-keys
  the shadowed imports to qualified atoms (`:"Mod#Name"`), and resolves qualified
  surface references + shadow diagnostics from the re-keyed env. The kernel/TCB
  (`lib/cure/core/*`) is never modified; this module only reads Core term shapes.
  """

  alias Cure.Core.{Env, Inductive}

  @doc """
  Substitute constructor/family atoms in a Core term per `atom_map`
  (`%{bare => rekeyed}`). Rewrites the three bare-atom term positions —
  `:data` heads, `:ctor` heads, and `:case` branch tags — and recurses through
  every structural node. Leaves `:global` (function references keep bare names)
  and all literals untouched. An atom absent from `atom_map` is passed through.
  """
  @spec rekey_term(term, %{atom() => atom()}) :: term when term: tuple()
  def rekey_term(term, m)

  def rekey_term({:data, n, ps, is}, m),
    do: {:data, Map.get(m, n, n), Enum.map(ps, &rekey_term(&1, m)), Enum.map(is, &rekey_term(&1, m))}

  def rekey_term({:ctor, n, args}, m),
    do: {:ctor, Map.get(m, n, n), Enum.map(args, &rekey_term(&1, m))}

  def rekey_term({:case, s, mo, brs}, m),
    do:
      {:case, rekey_term(s, m), rekey_term(mo, m),
       Enum.map(brs, fn {cn, ar, b} -> {Map.get(m, cn, cn), ar, rekey_term(b, m)} end)}

  def rekey_term({:pi, dom, cod}, m), do: {:pi, rekey_term(dom, m), rekey_term(cod, m)}
  def rekey_term({:lam, dom, body}, m), do: {:lam, rekey_term(dom, m), rekey_term(body, m)}
  def rekey_term({:sigma, a, b}, m), do: {:sigma, rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:app, f, a}, m), do: {:app, rekey_term(f, m), rekey_term(a, m)}
  def rekey_term({:pair, a, b}, m), do: {:pair, rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:fst, p}, m), do: {:fst, rekey_term(p, m)}
  def rekey_term({:snd, p}, m), do: {:snd, rekey_term(p, m)}
  def rekey_term({:eq, ty, a, b}, m), do: {:eq, rekey_term(ty, m), rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:refl, a}, m), do: {:refl, rekey_term(a, m)}

  def rekey_term({:rewrite, proof, motive, body}, m),
    do: {:rewrite, rekey_term(proof, m), rekey_term(motive, m), rekey_term(body, m)}

  def rekey_term({:prim, op, args}, m), do: {:prim, op, Enum.map(args, &rekey_term(&1, m))}

  # Leaves: :var, :type, :global, :int_type, :int_lit, :float_type, :float_lit.
  def rekey_term(leaf, _m), do: leaf

  @doc """
  Re-key every family named in `owned_family_names` within `env`'s slice to
  `:"<module_id>#<name>"`. Constructor *ownership* and constructor *names* are
  separate: a type-name collision re-keys the family id and every constructor's
  family pointer, but a constructor keeps its bare key unless its own name is in
  `shadowed_ctor_names`. This preserves Cure's rule that `type Nat = Zero | Suc`
  shadows the type name `Nat`, while bare `Z`/`S` may still refer to `Std.Nat`
  unless those constructor names are also redeclared locally.

  Rewrites every embedded Core term (family/ctor telescopes, ctor result
  indices/params, and ALL def bodies+types in the slice) via `rekey_term/2`.
  Colliding function names in `owned_def_names` additionally have their `defs`
  KEY (and their `certified` membership) moved to the qualified `:"Mod#name"`
  atom, so a shadowed import stays reachable only under its qualified key.
  """
  @spec rekey_module_env(Env.t(), String.t(), MapSet.t(atom())) :: Env.t()
  def rekey_module_env(env, module_id, owned_family_names),
    do:
      rekey_module_env(
        env,
        module_id,
        owned_family_names,
        owned_family_names
        |> Enum.flat_map(fn fname ->
          for {cname, ^fname} <- env.ctor_to_family, do: cname
        end)
        |> MapSet.new()
      )

  @spec rekey_module_env(Env.t(), String.t(), MapSet.t(atom()), MapSet.t(atom()), MapSet.t(atom())) ::
          Env.t()
  def rekey_module_env(
        %Env{} = env,
        module_id,
        owned_family_names,
        shadowed_ctor_names,
        owned_def_names \\ MapSet.new()
      ) do
    # Owned ctor names: ctors whose family is an owned family name.
    owned_ctor_names =
      for {cname, fname} <- env.ctor_to_family, MapSet.member?(owned_family_names, fname), into: MapSet.new(), do: cname

    rekeyed_ctor_names = MapSet.intersection(owned_ctor_names, shadowed_ctor_names)

    # bare -> rekeyed atom map covering owned families and only constructor names
    # that are shadowed as constructors.
    amap =
      Enum.reduce(owned_family_names, %{}, fn f, acc -> Map.put(acc, f, rekey_atom(module_id, f)) end)

    amap =
      Enum.reduce(rekeyed_ctor_names, amap, fn c, acc -> Map.put(acc, c, rekey_atom(module_id, c)) end)

    # Colliding function names: unlike ctors/families (leaf atoms rewritten inside
    # Core terms), a def is addressed by its `defs` KEY and `certified` membership,
    # both of which move to the qualified atom below.
    amap =
      Enum.reduce(owned_def_names, amap, fn d, acc -> Map.put(acc, d, rekey_atom(module_id, d)) end)

    %Env{
      env
      | families: rekey_families(env.families, owned_family_names, amap),
        ctors: rekey_ctors(env.ctors, rekeyed_ctor_names, amap),
        ctor_to_family: rekey_c2f(env.ctor_to_family, amap),
        defs: rekey_defs(env.defs, owned_def_names, module_id, amap),
        certified: rekey_certified(env.certified, owned_def_names, module_id),
        builtins: rekey_builtins(env.builtins, amap)
    }
  end

  defp rekey_atom(module_id, bare), do: String.to_atom(module_id <> "#" <> Atom.to_string(bare))

  defp rekey_families(families, owned, amap) do
    Map.new(families, fn {k, fam} ->
      if MapSet.member?(owned, k) do
        {Map.fetch!(amap, k),
         %{fam | name: Map.fetch!(amap, k),
                 params: rekey_tele(fam.params, amap), indices: rekey_tele(fam.indices, amap)}}
      else
        {k, %{fam | params: rekey_tele(fam.params, amap), indices: rekey_tele(fam.indices, amap)}}
      end
    end)
  end

  defp rekey_ctors(ctors, owned_ctor_names, amap) do
    Map.new(ctors, fn {k, c} ->
      c2 = %{c |
        name: Map.get(amap, c.name, c.name),
        args: rekey_tele(c.args, amap),
        result_indices: Enum.map(c.result_indices, &rekey_term(&1, amap)),
        result_params: Enum.map(c.result_params, &rekey_term(&1, amap))
      }

      if MapSet.member?(owned_ctor_names, k), do: {Map.fetch!(amap, k), c2}, else: {k, c2}
    end)
  end

  defp rekey_c2f(c2f, amap) do
    Map.new(c2f, fn {c, f} -> {Map.get(amap, c, c), Map.get(amap, f, f)} end)
  end

  # Rewrite embedded ctor/family references in every def's type+body (via `amap`),
  # AND move the KEY of an owned-and-colliding def to its qualified atom.
  defp rekey_defs(defs, owned_def_names, module_id, amap) do
    Map.new(defs, fn {k, d} ->
      d2 = %{d | type: rekey_term(d.type, amap), body: rekey_term(d.body, amap)}
      key = if MapSet.member?(owned_def_names, k), do: rekey_atom(module_id, k), else: k
      {key, d2}
    end)
  end

  # Move certified membership for owned-and-colliding defs to their qualified atom
  # so a re-keyed total function stays δ-reducible under its new key.
  defp rekey_certified(certified, owned_def_names, module_id) do
    (certified || MapSet.new())
    |> Enum.map(fn name ->
      if MapSet.member?(owned_def_names, name), do: rekey_atom(module_id, name), else: name
    end)
    |> MapSet.new()
  end

  defp rekey_tele(tele, amap), do: Enum.map(tele, fn {n, t} -> {n, rekey_term(t, amap)} end)

  defp rekey_builtins(builtins, amap),
    do: Map.new(builtins, fn {k, fid} -> {k, Map.get(amap, fid, fid)} end)

  @doc """
  Classify family-name collisions. A family name `N` collides when its set of
  sources — the distinct import modules that OWN it (declare it in their own
  AST) plus the local module if it declares `N` — has size ≥ 2. In every
  collision the winner of the unqualified name is the LOCAL module if present
  (only the local module can win); therefore every import owner of a colliding
  name is a loser. When no local declares a colliding name, the name is
  additionally `ambiguous` (unqualified use is an error, §3.4) — but its
  owners are still re-keyed so both stay reachable qualified.
  """
  @spec classify(%{atom() => MapSet.t(String.t())}, MapSet.t(atom())) :: %{
          losers: %{String.t() => MapSet.t(atom())},
          ambiguous: MapSet.t(atom())
        }
  def classify(family_owners, local_families) do
    Enum.reduce(family_owners, %{losers: %{}, ambiguous: MapSet.new()}, fn {name, owners}, acc ->
      local? = MapSet.member?(local_families, name)
      n_sources = MapSet.size(owners) + if local?, do: 1, else: 0

      cond do
        n_sources < 2 ->
          acc

        true ->
          losers =
            Enum.reduce(owners, acc.losers, fn mod, ls ->
              Map.update(ls, mod, MapSet.new([name]), &MapSet.put(&1, name))
            end)

          ambiguous = if local?, do: acc.ambiguous, else: MapSet.put(acc.ambiguous, name)
          %{losers: losers, ambiguous: ambiguous}
      end
    end)
  end

  @doc """
  Resolve a flattened dotted surface path (`"Std.Nat.Z"`) to a registry key,
  trying the qualified `:"Mod#Name"` key FIRST and a bare-atom key second (the
  ordering is load-bearing: under a local shadow the loser is only reachable at
  its qualified key, and a bare fallback must never grab the local winner —
  which is safe precisely because a shadowed import is always re-keyed, so its
  bare key is absent). `slot` selects type vs value candidate shapes.
  """
  @spec resolve_qualified(Env.t(), String.t(), :type | :value) :: {:ok, atom()} | :error
  def resolve_qualified(%Env{} = env, dotted, :value) do
    segs = String.split(dotted, ".")
    {mod_segs, [last]} = Enum.split(segs, length(segs) - 1)
    mod = Enum.join(mod_segs, ".")
    try_keys(env, [rekey_atom(mod, String.to_atom(last)), String.to_atom(last)], :value)
  end

  def resolve_qualified(%Env{} = env, dotted, :type) do
    segs = String.split(dotted, ".")
    last = List.last(segs)
    {mod_segs, [explicit_last]} = Enum.split(segs, length(segs) - 1)

    candidates = [
      # module==typename collapse: whole path is the module, name repeats the tail.
      rekey_atom(dotted, String.to_atom(last)),
      # explicit Mod.Type spelling.
      rekey_atom(Enum.join(mod_segs, "."), String.to_atom(explicit_last)),
      # unshadowed bare fallback.
      String.to_atom(last)
    ]

    try_keys(env, candidates, :type)
  end

  @doc """
  Uniform shadowed-but-present resolution (spec §3.3, per-name scoping as in
  Idris/Agda): a BARE name that is absent from the registry but present under
  exactly ONE re-keyed `:"Mod#name"` variant resolves to that variant. Exactly-one
  is required — `{:ambiguous, mods}` for ≥2 (the R7 path), `:none` for 0. Callers
  must apply this only AFTER confirming the bare name has no local winner and no
  unshadowed-import binding, so a redeclared ctor (still present under its bare
  key) never reaches this fallback (preserving R1).
  """
  @spec resolve_bare_shadowed(Env.t(), atom()) :: {:ok, atom()} | :none | {:ambiguous, [String.t()]}
  def resolve_bare_shadowed(%Env{families: families, ctors: ctors}, bare) do
    suffix = "#" <> Atom.to_string(bare)

    matches =
      (Map.keys(ctors) ++ Map.keys(families))
      |> Enum.flat_map(fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: [{String.trim_trailing(s, suffix), k}], else: []
      end)

    case matches do
      [{_mod, key}] -> {:ok, key}
      [] -> :none
      many -> {:ambiguous, Enum.map(many, fn {mod, _k} -> mod end)}
    end
  end

  @doc """
  If a bare constructor/family name was shadowed (re-keyed off the bare atom),
  find the re-keyed variant `:"Mod#bare"` still present in the env and report
  its origin module + re-keyed atom. Returns `:error` if no shadowed variant
  exists (the name is genuinely unknown, not shadowed).
  """
  @spec shadowed_origin(Env.t(), atom()) :: {:ok, String.t(), atom()} | :error
  def shadowed_origin(%Env{ctors: ctors, families: families, ctor_to_family: c2f}, bare) do
    suffix = "#" <> Atom.to_string(bare)

    match =
      Enum.find_value(Map.keys(ctors) ++ Map.keys(families), fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: {String.trim_trailing(s, suffix), k}, else: nil
      end)

    case match do
      {mod_id, key} -> {:ok, mod_id, key}
      nil -> shadowed_origin_from_family(c2f, bare)
    end
  end

  defp shadowed_origin_from_family(c2f, bare) do
    case Map.get(c2f, bare) do
      fam when is_atom(fam) ->
        fam
        |> Atom.to_string()
        |> String.split("#", parts: 2)
        |> case do
          [mod_id, _family] -> {:ok, mod_id, bare}
          _ -> :error
        end

      _ ->
        :error
    end
  end

  @doc """
  All origin modules that provide family `bare` under a re-keyed `:"Mod#bare"`
  family key. ≥2 ⇒ the unqualified name is ambiguous (no local winner claimed
  the bare key). Returns [] when the bare key is present (a winner exists) or
  the name is unknown.
  """
  @spec ambiguous_modules(Env.t(), atom()) :: [String.t()]
  def ambiguous_modules(%Env{families: families}, bare) do
    if Map.has_key?(families, bare) do
      []
    else
      suffix = "#" <> Atom.to_string(bare)

      families
      |> Map.keys()
      |> Enum.flat_map(fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: [String.trim_trailing(s, suffix)], else: []
      end)
    end
  end

  defp try_keys(env, keys, slot) do
    present? =
      case slot do
        :type -> fn k -> Inductive.family?(env, k) end
        :value -> fn k -> not is_nil(Inductive.get_ctor(env, k)) or Map.has_key?(env.defs, k) end
      end

    case Enum.find(keys, present?) do
      nil -> :error
      key -> {:ok, key}
    end
  end
end
