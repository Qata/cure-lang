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
end
