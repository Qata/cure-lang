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
