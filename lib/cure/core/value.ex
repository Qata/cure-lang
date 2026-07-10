defmodule Cure.Core.Value do
  @moduledoc """
  Semantic values for normalization-by-evaluation (design spec §4.5).

  `Eval.eval/2` turns a `Cure.Core.Term` into a `Value`; `Quote.reify/2` reads a
  `Value` back into a β-normal `Term`. Binders are represented by **closures**
  `{:closure, env, body_term}` (an environment plus an unevaluated body), and
  stuck computations by **neutrals** carrying a de Bruijn *level* head (read-back
  converts levels to indices).

  Value shapes:

    * `{:vtype, level}`                  universe
    * `{:vpi, dom_value, closure}`       Π type (closure = the codomain family)
    * `{:vlam, dom_value, closure}`      λ (domain kept so read-back is a true
                                         inverse — mirrors Idris's `Lam … ty`)
    * `{:vneutral, neutral}`             stuck term
    * `{:vdata, name, [value]}`          fully-applied family (params ++ indices)
    * `{:vctor, name, [value]}`          fully-applied constructor
    * `{:vnat, n}`                       compact Nat literal (`n >= 0`), defeq to
                                         the n-fold `S`-tower over `Z`

  Neutral shapes (a head plus eliminator spine):

    * `{:nvar, level}`                   free variable, de Bruijn *level*
    * `{:nglobal, name}`                 uncertified global (opaque until δ, M7)
    * `{:napp, neutral, value}`          stuck application
    * `{:ncase, neutral, motive_closure, branch_closures}`  stuck eliminator,
      `branch_closures :: [{ctor_name, arity, closure}]`
  """

  alias Cure.Core.{Term, Universe}

  @typedoc "A `:ncase` branch closure: constructor name, arity, and the branch's closure."
  @type branch_closure :: {atom(), non_neg_integer(), closure()}

  @typedoc "A binder closure: an environment plus an unevaluated body term."
  @type closure :: {:closure, [t()], Term.t()}

  @typedoc "A stuck computation: a head plus an eliminator spine."
  @type neutral ::
          {:nvar, non_neg_integer()}
          | {:nglobal, atom()}
          | {:napp, neutral(), t()}
          | {:ncase, neutral(), closure(), [branch_closure()]}

  @typedoc """
  A semantic value — the shapes above, as a closed union.

  Deliberately NOT `tuple()`, for the same reason as `Cure.Core.Term.t/0`:
  written loosely, Dialyzer and Elixir's set-theoretic checker cannot see that a
  wrong-arity `{:vpi, dom, cl}` is wrong, and a reshape of the taxonomy proceeds
  silently. Written precisely, both catch it statically.
  """
  @type t ::
          {:vtype, non_neg_integer()}
          | {:vpi, t(), closure()}
          | {:vlam, t(), closure()}
          | {:vneutral, neutral()}
          | {:vdata, atom(), [t()]}
          | {:vctor, atom(), [t()]}
          | {:vint_type}
          | {:vint, integer()}
          | {:vnat, non_neg_integer()}
          | {:vbounded, non_neg_integer()}
          | {:vfloat_type}
          | {:vfloat, float()}
          | {:vbinary_type}
          | {:vatom_type}
          | {:vatom, atom()}

  @doc "True when `value` is a structurally well-formed semantic value."
  @spec value?(term()) :: boolean()
  def value?({:vtype, level}),
    do: is_integer(level) and level >= 0 and level <= Universe.ceiling()

  def value?({:vpi, dom, cl}), do: value?(dom) and closure?(cl)
  def value?({:vlam, dom, cl}), do: value?(dom) and closure?(cl)
  def value?({:vneutral, n}), do: neutral?(n)
  def value?({:vdata, name, vs}), do: is_atom(name) and values?(vs)
  def value?({:vctor, name, vs}), do: is_atom(name) and values?(vs)
  def value?({:vint_type}), do: true
  def value?({:vint, n}), do: is_integer(n)
  # Compact Nat literal value (defeq to the n-fold `S`-tower over `Z`).
  def value?({:vnat, n}), do: is_integer(n) and n >= 0
  def value?({:vbounded, n}), do: is_integer(n) and n >= 0
  def value?({:vfloat_type}), do: true
  def value?({:vbinary_type}), do: true
  def value?({:vatom_type}), do: true
  def value?({:vatom, a}), do: is_atom(a)
  def value?({:vfloat, f}), do: is_float(f)
  def value?(_), do: false

  @doc "True when `neutral` is a structurally well-formed neutral (stuck) value."
  @spec neutral?(term()) :: boolean()
  def neutral?({:nvar, level}), do: is_integer(level) and level >= 0
  def neutral?({:nglobal, name}), do: is_atom(name)
  def neutral?({:napp, n, v}), do: neutral?(n) and value?(v)

  def neutral?({:ncase, n, motive_cl, branches}),
    do: neutral?(n) and closure?(motive_cl) and branch_closures?(branches)

  def neutral?(_), do: false

  @doc "True when `closure` is `{:closure, env, term}` with an env of values and a body term."
  @spec closure?(term()) :: boolean()
  def closure?({:closure, env, body}), do: is_list(env) and values?(env) and Term.term?(body)
  def closure?(_), do: false

  # -- helpers ----------------------------------------------------------------

  defp values?(list) when is_list(list), do: Enum.all?(list, &value?/1)
  defp values?(_), do: false

  defp branch_closures?(list) when is_list(list), do: Enum.all?(list, &branch_closure?/1)
  defp branch_closures?(_), do: false

  defp branch_closure?({ctor_name, arity, cl})
       when is_atom(ctor_name) and is_integer(arity) and arity >= 0,
       do: closure?(cl)

  defp branch_closure?(_), do: false
end
