defmodule Cure.Core.Quote do
  @moduledoc """
  Read-back (quote): convert a `Cure.Core.Value` into a **β-normal**
  `Cure.Core.Term` (design spec §4.5; mirrors Idris `Core/Normalise/Quote.idr`).

  `depth` is the number of binders entered so far. A neutral variable carries a
  de Bruijn *level*; read-back converts it to an index via `depth - level - 1`.
  Going under a binder, we apply the closure to a fresh neutral at the current
  level and reify the result at `depth + 1`, exactly as Idris's `quoteGenNF`
  does for `NBind` (and `quoteBinder` reifies the binder's domain type).

  η is **not** performed here — read-back stays untyped and β-normal. η-equality
  is decided in `Cure.Core.Conv` (it needs the neutral's type, which a `Value`
  does not carry).

  ## Signature-aware read-back (`sig`)

  A data VALUE `{:vdata, name, args}` flattens a family's parameters and indices
  into one arg list (M3.4). Without the family signature the split is not
  recoverable, so read-back defaults (`sig = nil`) to putting them all in the
  `params` slot with empty `indices` — the flat form that conversion compares
  (conversion never asks for the split, so this stays consistent). When a caller
  that DOES need the split passes the signature (`Env.t()`), the `{:vdata}`
  read-back recovers `{:data, name, params, indices}` from the family's parameter
  telescope length — Agda `getNumberOfParameters` / Lean `inductive_val.get_nparams`
  prior art. This is required by the kernel's motive-well-formedness check, which
  reifies indexed-family Eq endpoints and re-`check`s them against their type (a
  collapsed split otherwise fails with an arity error and false-rejects the motive).
  """

  alias Cure.Core.Eval

  @doc """
  Read a value back into a β-normal term. `depth` = binders entered so far.
  `sig` (optional) is the inductive signature used to recover the param/index
  split of data values; `nil` (default) keeps the flat read-back.
  """
  @spec reify(Cure.Core.Value.t(), non_neg_integer(), Cure.Core.Env.t() | nil) ::
          Cure.Core.Term.t()
  def reify(value, depth \\ 0, sig \\ nil)

  def reify({:vtype, level}, _depth, _sig), do: {:type, level}

  def reify({:vpi, dom, {:closure, env, cod}}, depth, sig) do
    body = Eval.eval(cod, [{:vneutral, {:nvar, depth}} | env])
    {:pi, reify(dom, depth, sig), reify(body, depth + 1, sig)}
  end

  def reify({:vlam, dom, {:closure, env, b}}, depth, sig) do
    body = Eval.eval(b, [{:vneutral, {:nvar, depth}} | env])
    {:lam, reify(dom, depth, sig), reify(body, depth + 1, sig)}
  end

  def reify({:vsigma, dom, {:closure, env, b}}, depth, sig) do
    body = Eval.eval(b, [{:vneutral, {:nvar, depth}} | env])
    {:sigma, reify(dom, depth, sig), reify(body, depth + 1, sig)}
  end

  def reify({:vpair, a, b}, depth, sig), do: {:pair, reify(a, depth, sig), reify(b, depth, sig)}

  # Data value read-back. With a signature the param/index split is recovered from
  # the family's parameter telescope length; without one, all args stay in `params`
  # (the flat form conversion compares). See the moduledoc.
  def reify({:vdata, name, vs}, depth, sig) do
    {params, indices} = split_data_args(name, vs, sig)
    {:data, name, Enum.map(params, &reify(&1, depth, sig)), Enum.map(indices, &reify(&1, depth, sig))}
  end

  def reify({:vctor, name, vs}, depth, sig), do: {:ctor, name, Enum.map(vs, &reify(&1, depth, sig))}

  def reify({:vint_type}, _depth, _sig), do: {:int_type}
  def reify({:vint, n}, _depth, _sig), do: {:int_lit, n}
  def reify({:vfloat_type}, _depth, _sig), do: {:float_type}
  def reify({:vfloat, f}, _depth, _sig), do: {:float_lit, f}

  def reify({:vneutral, n}, depth, sig), do: reify_neutral(n, depth, sig)

  # -- data param/index split -------------------------------------------------

  # Recover a data value's (params, indices) split. `nil` signature → cannot split,
  # so all args are params (flat read-back). With a signature, the first
  # `length(family.params)` args are parameters and the rest are indices (Agda
  # `getNumberOfParameters` / Lean `get_nparams`). An unknown family also stays flat
  # — never unsound, at worst the pre-existing collapse.
  defp split_data_args(_name, vs, nil), do: {vs, []}

  defp split_data_args(name, vs, sig) do
    case Cure.Core.Inductive.get_family(sig, name) do
      %{params: ptele} -> Enum.split(vs, length(ptele))
      _ -> {vs, []}
    end
  end

  # -- neutrals ---------------------------------------------------------------

  defp reify_neutral({:nvar, level}, depth, _sig), do: {:var, depth - level - 1}
  defp reify_neutral({:nglobal, name}, _depth, _sig), do: {:global, name}

  defp reify_neutral({:napp, n, v}, depth, sig),
    do: {:app, reify_neutral(n, depth, sig), reify(v, depth, sig)}

  defp reify_neutral({:nfst, n}, depth, sig), do: {:fst, reify_neutral(n, depth, sig)}
  defp reify_neutral({:nsnd, n}, depth, sig), do: {:snd, reify_neutral(n, depth, sig)}

  defp reify_neutral({:nprim, op, args}, depth, sig),
    do: {:prim, op, Enum.map(args, &reify(&1, depth, sig))}

  defp reify_neutral({:ncase, neutral, motive_cl, branch_cls}, depth, sig) do
    scrut = reify_neutral(neutral, depth, sig)
    motive = reify(instantiate(motive_cl), depth, sig)
    branches = Enum.map(branch_cls, fn {c, ar, cl} -> {c, ar, reify_branch(cl, ar, depth, sig)} end)
    {:case, scrut, motive, branches}
  end

  # Evaluate a closure body in its captured environment (no extra binder).
  defp instantiate({:closure, env, term}), do: Eval.eval(term, env)

  # Read a branch-body closure back under the constructor's `arity` binders.
  defp reify_branch({:closure, env, body}, arity, depth, sig) do
    fresh = for i <- 0..(arity - 1)//1, do: {:vneutral, {:nvar, depth + i}}
    ext = Enum.reverse(fresh)
    reify(Eval.eval(body, ext ++ env), depth + arity, sig)
  end
end
