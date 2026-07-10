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
  every structural node. Leaves `:global` (function references keep bare names —
  use `rekey_term/3` to also re-key colliding def references) and all literals
  untouched. An atom absent from `atom_map` is passed through.
  """
  @spec rekey_term(term, %{atom() => atom()}) :: term when term: tuple()
  def rekey_term(term, m), do: rekey_term(term, m, %{})

  @doc """
  As `rekey_term/2`, but additionally re-keys `{:global, name}` def references
  through `def_map` (`%{bare_def => :"Mod#def"}`).

  A def is normally addressed by its `defs` KEY, which moves to `:"Mod#name"`
  when the def collides (see `rekey_defs`). A reference embedded in ANOTHER
  slice's body must follow that move, or it dangles (emit fails with
  `{name, arity}` undefined). `def_map` is kept SEPARATE from the type/ctor
  `atom_map` on purpose: a function may share a name with an unrelated
  constructor being re-keyed, and only the def-reference position may consult
  the def rename — never a `:data`/`:ctor`/`:case` tag.
  """
  @spec rekey_term(term, %{atom() => atom()}, %{atom() => atom()}) :: term when term: tuple()
  def rekey_term({:data, n, ps, is}, m, d),
    do: {:data, Map.get(m, n, n), Enum.map(ps, &rekey_term(&1, m, d)), Enum.map(is, &rekey_term(&1, m, d))}

  def rekey_term({:ctor, n, args}, m, d),
    do: {:ctor, Map.get(m, n, n), Enum.map(args, &rekey_term(&1, m, d))}

  def rekey_term({:case, s, mo, brs}, m, d),
    do:
      {:case, rekey_term(s, m, d), rekey_term(mo, m, d),
       Enum.map(brs, fn {cn, ar, b} -> {Map.get(m, cn, cn), ar, rekey_term(b, m, d)} end)}

  def rekey_term({:pi, dom, cod}, m, d), do: {:pi, rekey_term(dom, m, d), rekey_term(cod, m, d)}
  def rekey_term({:lam, dom, body}, m, d), do: {:lam, rekey_term(dom, m, d), rekey_term(body, m, d)}
  def rekey_term({:app, f, a}, m, d), do: {:app, rekey_term(f, m, d), rekey_term(a, m, d)}

  def rekey_term({:global, n}, _m, d), do: {:global, Map.get(d, n, n)}

  # Leaves: :var, :type, :int_type, :int_lit, :float_type, :float_lit.
  def rekey_term(leaf, _m, _d), do: leaf

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

    # Colliding function names: a def is addressed by its `defs` KEY and
    # `certified` membership (both moved to the qualified atom below), AND by
    # `{:global, name}` references embedded in OTHER slices' bodies. The latter
    # are rewritten inside Core terms via a SEPARATE `def_map` — kept apart from
    # the family/ctor `amap` so a function sharing a name with a re-keyed
    # constructor is not swept up in a `:data`/`:ctor`/`:case` position.
    def_map =
      Enum.reduce(owned_def_names, %{}, fn d, acc -> Map.put(acc, d, rekey_atom(module_id, d)) end)

    %Env{
      env
      | families: rekey_families(env.families, owned_family_names, amap, def_map),
        ctors: rekey_ctors(env.ctors, rekeyed_ctor_names, amap, def_map),
        ctor_to_family: rekey_c2f(env.ctor_to_family, amap),
        defs: rekey_defs(env.defs, owned_def_names, module_id, amap, def_map),
        certified: rekey_certified(env.certified, owned_def_names, module_id),
        builtins: rekey_builtins(env.builtins, amap)
    }
  end

  defp rekey_atom(module_id, bare), do: String.to_atom(module_id <> "#" <> Atom.to_string(bare))

  defp rekey_families(families, owned, amap, def_map) do
    Map.new(families, fn {k, fam} ->
      if MapSet.member?(owned, k) do
        {Map.fetch!(amap, k),
         %{fam | name: Map.fetch!(amap, k),
                 params: rekey_tele(fam.params, amap, def_map), indices: rekey_tele(fam.indices, amap, def_map)}}
      else
        {k, %{fam | params: rekey_tele(fam.params, amap, def_map), indices: rekey_tele(fam.indices, amap, def_map)}}
      end
    end)
  end

  defp rekey_ctors(ctors, owned_ctor_names, amap, def_map) do
    Map.new(ctors, fn {k, c} ->
      c2 = %{c |
        name: Map.get(amap, c.name, c.name),
        args: rekey_tele(c.args, amap, def_map),
        result_indices: Enum.map(c.result_indices, &rekey_term(&1, amap, def_map)),
        result_params: Enum.map(c.result_params, &rekey_term(&1, amap, def_map))
      }

      if MapSet.member?(owned_ctor_names, k), do: {Map.fetch!(amap, k), c2}, else: {k, c2}
    end)
  end

  defp rekey_c2f(c2f, amap) do
    Map.new(c2f, fn {c, f} -> {Map.get(amap, c, c), Map.get(amap, f, f)} end)
  end

  # Rewrite embedded ctor/family references (via `amap`) AND colliding def
  # references (via `def_map`) in every def's type+body, AND move the KEY of an
  # owned-and-colliding def to its qualified atom.
  defp rekey_defs(defs, owned_def_names, module_id, amap, def_map) do
    Map.new(defs, fn {k, d} ->
      d2 = %{d | type: rekey_term(d.type, amap, def_map), body: rekey_term(d.body, amap, def_map)}
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

  defp rekey_tele(tele, amap, def_map),
    do: Enum.map(tele, fn {n, t} -> {n, rekey_term(t, amap, def_map)} end)

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
  def resolve_bare_shadowed(%Env{families: families, ctors: ctors, defs: defs}, bare) do
    suffix = "#" <> Atom.to_string(bare)

    matches =
      (Map.keys(ctors) ++ Map.keys(families) ++ Map.keys(defs))
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
  All origin modules that provide `bare` under a re-keyed `:"Mod#bare"` key in
  EITHER namespace — inductive families or plain global defs (Approach B re-keys
  both on collision). ≥2 ⇒ the unqualified name is ambiguous (no local winner
  claimed the bare key). Returns [] when the bare key is present in either map (a
  winner exists) or the name is unknown. Families and defs are classified
  independently, so a bare name reported here is ambiguous across whichever
  namespaces re-keyed it; Cure's capitalized-type / lowercase-def convention
  makes a cross-namespace spelling coincidence practically impossible (§3.4).
  """
  @spec ambiguous_modules(Env.t(), atom()) :: [String.t()]
  def ambiguous_modules(%Env{families: families, defs: defs}, bare) do
    if Map.has_key?(families, bare) or Map.has_key?(defs, bare) do
      []
    else
      suffix = "#" <> Atom.to_string(bare)

      (Map.keys(families) ++ Map.keys(defs))
      |> Enum.flat_map(fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: [String.trim_trailing(s, suffix)], else: []
      end)
      |> Enum.uniq()
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
