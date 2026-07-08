defmodule Cure.Elab.Subst do
  @moduledoc """
  De Bruijn shifting and telescope instantiation for *elaborator* terms — Core
  terms that may still carry unsolved metavariables `{:meta, id}` (design spec
  §5.3).

  The trusted kernel's `Core.Term.shift`/`subst` cannot be reused here: they do
  not know about `{:meta, …}` (metavariables never reach the kernel), and the
  kernel instantiates telescopes by evaluating in a value environment — a path
  that would drag metavariables into the trusted evaluator. So the untrusted
  elaborator carries its own meta-aware substitution.

  `instantiate/2` replaces a term's leading de Bruijn binders with a list of
  closed values in telescope order (`values[0]` is the outermost binder), and
  strengthens any variable that referred past the telescope. This is the operation
  constructor-application inference uses to specialise each argument's expected
  type given the arguments chosen so far.
  """

  @type uterm :: Cure.Core.Term.t() | {:meta, non_neg_integer()}

  @doc """
  Instantiate the outermost `length(values)` binders of `term` with `values`
  (telescope order: `values[0]` replaces the outermost binder). Variables beyond
  the telescope are strengthened by `length(values)`.
  """
  @spec instantiate(uterm(), [uterm()]) :: uterm()
  def instantiate(term, values) do
    env = Enum.reverse(values)
    replace(term, env, length(env), 0)
  end

  # `env` maps de Bruijn index j (0-based, innermost telescope binder first) to
  # its replacement; `k` = telescope size; `depth` = binders crossed so far.
  defp replace({:var, i}, env, k, depth) do
    cond do
      i < depth -> {:var, i}
      i - depth < k -> shift(Enum.at(env, i - depth), depth, 0)
      true -> {:var, i - k}
    end
  end

  defp replace({:meta, _} = m, _env, _k, _depth), do: m
  defp replace({:type, _} = t, _env, _k, _depth), do: t
  defp replace({:global, _} = g, _env, _k, _depth), do: g

  defp replace({:pi, d, c}, env, k, depth),
    do: {:pi, replace(d, env, k, depth), replace(c, env, k, depth + 1)}

  defp replace({:lam, d, b}, env, k, depth),
    do: {:lam, replace(d, env, k, depth), replace(b, env, k, depth + 1)}


  defp replace({:app, f, x}, env, k, depth),
    do: {:app, replace(f, env, k, depth), replace(x, env, k, depth)}


  defp replace({:data, n, ps, is}, env, k, depth),
    do: {:data, n, Enum.map(ps, &replace(&1, env, k, depth)), Enum.map(is, &replace(&1, env, k, depth))}

  defp replace({:ctor, n, args}, env, k, depth),
    do: {:ctor, n, Enum.map(args, &replace(&1, env, k, depth))}

  defp replace({:case, s, m, brs}, env, k, depth) do
    {:case, replace(s, env, k, depth), replace(m, env, k, depth),
     Enum.map(brs, fn {cn, ar, b} -> {cn, ar, replace(b, env, k, depth + ar)} end)}
  end

  defp replace({:prim, op, args}, env, k, depth),
    do: {:prim, op, Enum.map(args, &replace(&1, env, k, depth))}

  defp replace(other, _env, _k, _depth), do: other

  @doc "Shift free de Bruijn variables of a (meta-bearing) term above `cutoff` by `amount`."
  @spec shift(uterm(), integer(), non_neg_integer()) :: uterm()
  def shift(term, 0, _cutoff), do: term

  def shift({:var, i}, amount, cutoff) when i >= cutoff, do: {:var, i + amount}
  def shift({:var, _} = v, _amount, _cutoff), do: v
  def shift({:meta, _} = m, _amount, _cutoff), do: m
  def shift({:type, _} = t, _amount, _cutoff), do: t
  def shift({:global, _} = g, _amount, _cutoff), do: g

  def shift({:pi, d, c}, amount, cutoff),
    do: {:pi, shift(d, amount, cutoff), shift(c, amount, cutoff + 1)}

  def shift({:lam, d, b}, amount, cutoff),
    do: {:lam, shift(d, amount, cutoff), shift(b, amount, cutoff + 1)}


  def shift({:app, f, x}, amount, cutoff),
    do: {:app, shift(f, amount, cutoff), shift(x, amount, cutoff)}


  def shift({:data, n, ps, is}, amount, cutoff),
    do: {:data, n, Enum.map(ps, &shift(&1, amount, cutoff)), Enum.map(is, &shift(&1, amount, cutoff))}

  def shift({:ctor, n, args}, amount, cutoff),
    do: {:ctor, n, Enum.map(args, &shift(&1, amount, cutoff))}

  def shift({:case, s, m, brs}, amount, cutoff) do
    {:case, shift(s, amount, cutoff), shift(m, amount, cutoff),
     Enum.map(brs, fn {cn, ar, b} -> {cn, ar, shift(b, amount, cutoff + ar)} end)}
  end

  def shift({:prim, op, args}, amount, cutoff),
    do: {:prim, op, Enum.map(args, &shift(&1, amount, cutoff))}

  def shift(other, _amount, _cutoff), do: other
end
