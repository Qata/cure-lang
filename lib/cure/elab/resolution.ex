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
  Re-key every family named in `owned_family_names` (and each of its
  constructors) within `env`'s slice to `:"<module_id>#<name>"`. Renames the
  `families`/`ctors`/`ctor_to_family` map keys, updates each record's `:name`
  field, and rewrites every embedded Core term (family/ctor telescopes,
  ctor result indices/params, and ALL def bodies+types in the slice) via
  `rekey_term/2`. Families/ctors NOT owned are left untouched. Functions keep
  their bare `defs` keys (only embedded family/ctor references are rewritten).
  """
  @spec rekey_module_env(Env.t(), String.t(), MapSet.t(atom())) :: Env.t()
  def rekey_module_env(%Env{} = env, module_id, owned_family_names) do
    # Owned ctor names: ctors whose family is an owned family name.
    owned_ctor_names =
      for {cname, fname} <- env.ctor_to_family, MapSet.member?(owned_family_names, fname), into: MapSet.new(), do: cname

    # bare -> rekeyed atom map covering both owned families and their ctors.
    amap =
      Enum.reduce(owned_family_names, %{}, fn f, acc -> Map.put(acc, f, rekey_atom(module_id, f)) end)

    amap =
      Enum.reduce(owned_ctor_names, amap, fn c, acc -> Map.put(acc, c, rekey_atom(module_id, c)) end)

    %Env{
      env
      | families: rekey_families(env.families, owned_family_names, amap),
        ctors: rekey_ctors(env.ctors, owned_ctor_names, amap),
        ctor_to_family: rekey_c2f(env.ctor_to_family, amap),
        defs: rekey_defs(env.defs, amap)
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

  defp rekey_defs(defs, amap) do
    Map.new(defs, fn {k, d} ->
      {k, %{d | type: rekey_term(d.type, amap), body: rekey_term(d.body, amap)}}
    end)
  end

  defp rekey_tele(tele, amap), do: Enum.map(tele, fn {n, t} -> {n, rekey_term(t, amap)} end)

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
end
