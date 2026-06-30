defmodule Cure.Core.Term do
  @moduledoc """
  Explicit, fully-annotated Core terms for the trusted dependent-type kernel.

  Terms are plain tagged tuples using de Bruijn indices for bound variables.
  This is the soundness-critical representation described in the design spec
  §4.1; it deliberately carries no implicits, holes, or erasure annotations
  (those live only in the surface/elaborator) — a checked Core term is fully
  explicit and fully relevant.

  Node taxonomy (de Bruijn):

    * `{:type, level}`                       universe, `level` in 0..2
    * `{:var, k}`                            bound variable, de Bruijn index `k >= 0`
    * `{:pi, dom, cod}`                      dependent function type (binds in `cod`)
    * `{:lam, dom, body}`                    lambda (binds in `body`)
    * `{:app, f, a}`                         application
    * `{:sigma, a, b}`                       dependent pair type (binds in `b`)
    * `{:pair, a, b}`                        pair introduction
    * `{:fst, p}` / `{:snd, p}`              projections
    * `{:data, name, params, indices}`       family applied to params + indices
    * `{:ctor, name, args}`                  data constructor application
    * `{:case, scrut, motive, branches}`     dependent eliminator;
                                             `branches :: [{ctor_name, arity, body}]`
    * `{:global, name}`                      reference to a global def
    * `{:eq, ty, a, b}`                      propositional equality type
    * `{:refl, a}`                           reflexivity proof
    * `{:rewrite, proof, motive, body}`      transport / subst
  """

  @ceiling 2

  @typedoc "A Core term (see the module doc for the node taxonomy)."
  @type t :: tuple()

  @doc "Highest universe level (inclusive). The fixed hierarchy is `Type 0 : Type 1 : Type 2`."
  @spec ceiling() :: non_neg_integer()
  def ceiling, do: @ceiling

  @doc """
  True when `term` is a structurally well-formed Core term.

  This is a shape check only — it validates node arities, the universe-level
  bound (`0..#{@ceiling}`), and non-negative de Bruijn indices, recursively.
  It does not type-check; that is the kernel's job.
  """
  @spec term?(term()) :: boolean()
  def term?({:type, level}), do: is_integer(level) and level >= 0 and level <= @ceiling
  def term?({:var, k}), do: is_integer(k) and k >= 0
  def term?({:pi, dom, cod}), do: term?(dom) and term?(cod)
  def term?({:lam, dom, body}), do: term?(dom) and term?(body)
  def term?({:app, f, a}), do: term?(f) and term?(a)
  def term?({:sigma, a, b}), do: term?(a) and term?(b)
  def term?({:pair, a, b}), do: term?(a) and term?(b)
  def term?({:fst, p}), do: term?(p)
  def term?({:snd, p}), do: term?(p)

  def term?({:data, name, params, indices}),
    do: is_atom(name) and terms?(params) and terms?(indices)

  def term?({:ctor, name, args}), do: is_atom(name) and terms?(args)

  def term?({:case, scrut, motive, branches}),
    do: term?(scrut) and term?(motive) and branches?(branches)

  def term?({:global, name}), do: is_atom(name)
  def term?({:eq, ty, a, b}), do: term?(ty) and term?(a) and term?(b)
  def term?({:refl, a}), do: term?(a)

  def term?({:rewrite, proof, motive, body}),
    do: term?(proof) and term?(motive) and term?(body)

  def term?(_), do: false

  # -- de Bruijn shift / substitution -----------------------------------------
  #
  # Binder convention: `:pi`/`:lam`/`:sigma` introduce exactly one binder in
  # their codomain/body. A `:case` branch `{ctor, arity, body}` binds `arity`
  # variables in `body`. Motives (`:case`/`:rewrite`) are represented as
  # lambda-chains, so their binders are the ordinary `:lam` nodes inside them
  # and need no special counting here (confirmed by the M4 case-eliminator).

  @doc "Lift every free de Bruijn variable (index ≥ `cutoff`) by `amount`."
  @spec shift(t(), integer(), non_neg_integer()) :: t()
  def shift(term, amount, cutoff \\ 0)

  def shift({:var, k}, amount, cutoff) when k >= cutoff, do: {:var, k + amount}
  def shift({:var, _} = v, _amount, _cutoff), do: v
  def shift({:type, _} = t, _amount, _cutoff), do: t
  def shift({:global, _} = t, _amount, _cutoff), do: t
  def shift({:pi, dom, cod}, a, c), do: {:pi, shift(dom, a, c), shift(cod, a, c + 1)}
  def shift({:lam, dom, body}, a, c), do: {:lam, shift(dom, a, c), shift(body, a, c + 1)}
  def shift({:sigma, x, y}, a, c), do: {:sigma, shift(x, a, c), shift(y, a, c + 1)}
  def shift({:app, f, x}, a, c), do: {:app, shift(f, a, c), shift(x, a, c)}
  def shift({:pair, x, y}, a, c), do: {:pair, shift(x, a, c), shift(y, a, c)}
  def shift({:fst, p}, a, c), do: {:fst, shift(p, a, c)}
  def shift({:snd, p}, a, c), do: {:snd, shift(p, a, c)}

  def shift({:data, n, ps, is}, a, c),
    do: {:data, n, Enum.map(ps, &shift(&1, a, c)), Enum.map(is, &shift(&1, a, c))}

  def shift({:ctor, n, args}, a, c), do: {:ctor, n, Enum.map(args, &shift(&1, a, c))}

  def shift({:case, s, m, brs}, a, c),
    do:
      {:case, shift(s, a, c), shift(m, a, c),
       Enum.map(brs, fn {cn, ar, b} -> {cn, ar, shift(b, a, c + ar)} end)}

  def shift({:eq, ty, x, y}, a, c), do: {:eq, shift(ty, a, c), shift(x, a, c), shift(y, a, c)}
  def shift({:refl, x}, a, c), do: {:refl, shift(x, a, c)}

  def shift({:rewrite, p, m, b}, a, c),
    do: {:rewrite, shift(p, a, c), shift(m, a, c), shift(b, a, c)}

  @doc """
  Substitute the de Bruijn index `j` with `replacement` everywhere it occurs.

  Descends under binders, incrementing the target index and shifting the
  replacement so its free variables are not captured. This is a targeted
  substitution (it replaces index `j`; it does not renumber the others).
  """
  @spec subst(t(), non_neg_integer(), t()) :: t()
  def subst({:var, k}, j, r) when k == j, do: r
  def subst({:var, _} = v, _j, _r), do: v
  def subst({:type, _} = t, _j, _r), do: t
  def subst({:global, _} = t, _j, _r), do: t

  def subst({:pi, dom, cod}, j, r),
    do: {:pi, subst(dom, j, r), subst(cod, j + 1, shift(r, 1, 0))}

  def subst({:lam, dom, body}, j, r),
    do: {:lam, subst(dom, j, r), subst(body, j + 1, shift(r, 1, 0))}

  def subst({:sigma, x, y}, j, r),
    do: {:sigma, subst(x, j, r), subst(y, j + 1, shift(r, 1, 0))}

  def subst({:app, f, x}, j, r), do: {:app, subst(f, j, r), subst(x, j, r)}
  def subst({:pair, x, y}, j, r), do: {:pair, subst(x, j, r), subst(y, j, r)}
  def subst({:fst, p}, j, r), do: {:fst, subst(p, j, r)}
  def subst({:snd, p}, j, r), do: {:snd, subst(p, j, r)}

  def subst({:data, n, ps, is}, j, r),
    do: {:data, n, Enum.map(ps, &subst(&1, j, r)), Enum.map(is, &subst(&1, j, r))}

  def subst({:ctor, n, args}, j, r), do: {:ctor, n, Enum.map(args, &subst(&1, j, r))}

  def subst({:case, s, m, brs}, j, r),
    do:
      {:case, subst(s, j, r), subst(m, j, r),
       Enum.map(brs, fn {cn, ar, b} -> {cn, ar, subst(b, j + ar, shift(r, ar, 0))} end)}

  def subst({:eq, ty, x, y}, j, r),
    do: {:eq, subst(ty, j, r), subst(x, j, r), subst(y, j, r)}

  def subst({:refl, x}, j, r), do: {:refl, subst(x, j, r)}

  def subst({:rewrite, p, m, b}, j, r),
    do: {:rewrite, subst(p, j, r), subst(m, j, r), subst(b, j, r)}

  # -- helpers ----------------------------------------------------------------

  defp terms?(list) when is_list(list), do: Enum.all?(list, &term?/1)
  defp terms?(_), do: false

  defp branches?(list) when is_list(list), do: Enum.all?(list, &branch?/1)
  defp branches?(_), do: false

  defp branch?({ctor_name, arity, body})
       when is_atom(ctor_name) and is_integer(arity) and arity >= 0,
       do: term?(body)

  defp branch?(_), do: false
end
