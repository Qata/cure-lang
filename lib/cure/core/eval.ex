defmodule Cure.Core.Eval do
  @moduledoc """
  Normalization-by-evaluation: evaluate a `Cure.Core.Term` into a
  `Cure.Core.Value` under an environment (design spec §4.5).

  The environment is a `[value]` indexed by de Bruijn index — `var 0` is the
  most-recently-bound variable, at the head of the list. Binders evaluate to
  closures that capture the current environment; β/ι reduction happens eagerly
  via `apply/2` and the projection helpers.

  δ-unfolding of `:global` heads is **gated**: until a global is certified total
  (milestone M7), it evaluates to an opaque neutral `{:nglobal, name}`. `:case`
  (ι on constructors) is added in M4 and `:eq`/`:refl`/`:rewrite` in M6; this
  module covers the Π/λ/Σ/projection fragment.
  """

  # We define a local `apply/2`; keep it from clashing with Kernel.apply/2.
  import Kernel, except: [apply: 2]

  @doc "Evaluate `term` under `env` (a `[value]` indexed by de Bruijn index)."
  @spec eval(Cure.Core.Term.t(), [Cure.Core.Value.t()]) :: Cure.Core.Value.t()
  def eval({:type, level}, _env), do: {:vtype, level}

  def eval({:var, k}, env) do
    case Enum.at(env, k) do
      nil -> {:vneutral, {:nvar, k}}
      v -> v
    end
  end

  def eval({:pi, dom, cod}, env), do: {:vpi, eval(dom, env), {:closure, env, cod}}
  def eval({:lam, _dom, body}, env), do: {:vlam, {:closure, env, body}}
  def eval({:sigma, a, b}, env), do: {:vsigma, eval(a, env), {:closure, env, b}}
  def eval({:app, f, a}, env), do: apply(eval(f, env), eval(a, env))
  def eval({:pair, a, b}, env), do: {:vpair, eval(a, env), eval(b, env)}
  def eval({:fst, p}, env), do: vfst(eval(p, env))
  def eval({:snd, p}, env), do: vsnd(eval(p, env))

  def eval({:data, name, params, indices}, env),
    do: {:vdata, name, Enum.map(params ++ indices, &eval(&1, env))}

  def eval({:ctor, name, args}, env), do: {:vctor, name, Enum.map(args, &eval(&1, env))}

  # Opaque until the global is certified total (M7 gates δ here).
  def eval({:global, name}, _env), do: {:vneutral, {:nglobal, name}}

  @doc """
  Apply a function value to an argument value, performing β-reduction.

  A `:vlam` reduces by evaluating its body in the captured environment extended
  with the argument; a neutral function accumulates the argument on its spine.
  """
  @spec apply(Cure.Core.Value.t(), Cure.Core.Value.t()) :: Cure.Core.Value.t()
  def apply({:vlam, {:closure, env, body}}, varg), do: eval(body, [varg | env])
  def apply({:vneutral, n}, varg), do: {:vneutral, {:napp, n, varg}}

  # -- projection ι -----------------------------------------------------------

  defp vfst({:vpair, a, _b}), do: a
  defp vfst({:vneutral, n}), do: {:vneutral, {:nfst, n}}

  defp vsnd({:vpair, _a, b}), do: b
  defp vsnd({:vneutral, n}), do: {:vneutral, {:nsnd, n}}
end
