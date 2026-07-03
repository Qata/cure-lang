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
  """

  alias Cure.Core.Eval

  @doc "Read a value back into a β-normal term. `depth` = binders entered so far."
  @spec reify(Cure.Core.Value.t(), non_neg_integer()) :: Cure.Core.Term.t()
  def reify(value, depth \\ 0)

  def reify({:vtype, level}, _depth), do: {:type, level}

  def reify({:vpi, dom, {:closure, env, cod}}, depth) do
    body = Eval.eval(cod, [{:vneutral, {:nvar, depth}} | env])
    {:pi, reify(dom, depth), reify(body, depth + 1)}
  end

  def reify({:vlam, dom, {:closure, env, b}}, depth) do
    body = Eval.eval(b, [{:vneutral, {:nvar, depth}} | env])
    {:lam, reify(dom, depth), reify(body, depth + 1)}
  end

  def reify({:vsigma, dom, {:closure, env, b}}, depth) do
    body = Eval.eval(b, [{:vneutral, {:nvar, depth}} | env])
    {:sigma, reify(dom, depth), reify(body, depth + 1)}
  end

  def reify({:vpair, a, b}, depth), do: {:pair, reify(a, depth), reify(b, depth)}

  # The value flattens a family's params and indices into one arg list (M3.4);
  # the split is not recoverable here, so read-back puts them all in `params`.
  # Consumers (conversion) compare the flat spine, so this is consistent.
  def reify({:vdata, name, vs}, depth), do: {:data, name, Enum.map(vs, &reify(&1, depth)), []}
  def reify({:vctor, name, vs}, depth), do: {:ctor, name, Enum.map(vs, &reify(&1, depth))}

  def reify({:veq, ty, a, b}, depth),
    do: {:eq, reify(ty, depth), reify(a, depth), reify(b, depth)}

  def reify({:vrefl, a}, depth), do: {:refl, reify(a, depth)}

  def reify({:vint_type}, _depth), do: {:int_type}
  def reify({:vint, n}, _depth), do: {:int_lit, n}
  def reify({:vfloat_type}, _depth), do: {:float_type}
  def reify({:vfloat, f}, _depth), do: {:float_lit, f}

  def reify({:vneutral, n}, depth), do: reify_neutral(n, depth)

  # -- neutrals ---------------------------------------------------------------

  defp reify_neutral({:nvar, level}, depth), do: {:var, depth - level - 1}
  defp reify_neutral({:nglobal, name}, _depth), do: {:global, name}

  defp reify_neutral({:napp, n, v}, depth),
    do: {:app, reify_neutral(n, depth), reify(v, depth)}

  defp reify_neutral({:nfst, n}, depth), do: {:fst, reify_neutral(n, depth)}
  defp reify_neutral({:nsnd, n}, depth), do: {:snd, reify_neutral(n, depth)}

  defp reify_neutral({:nprim, op, args}, depth),
    do: {:prim, op, Enum.map(args, &reify(&1, depth))}

  defp reify_neutral({:ncase, neutral, motive_cl, branch_cls}, depth) do
    scrut = reify_neutral(neutral, depth)
    motive = reify(instantiate(motive_cl), depth)
    branches = Enum.map(branch_cls, fn {c, ar, cl} -> {c, ar, reify_branch(cl, ar, depth)} end)
    {:case, scrut, motive, branches}
  end

  # Evaluate a closure body in its captured environment (no extra binder).
  defp instantiate({:closure, env, term}), do: Eval.eval(term, env)

  # Read a branch-body closure back under the constructor's `arity` binders.
  defp reify_branch({:closure, env, body}, arity, depth) do
    fresh = for i <- 0..(arity - 1)//1, do: {:vneutral, {:nvar, depth + i}}
    ext = Enum.reverse(fresh)
    reify(Eval.eval(body, ext ++ env), depth + arity)
  end
end
