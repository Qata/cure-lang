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
  def eval({:lam, dom, body}, env), do: {:vlam, eval(dom, env), {:closure, env, body}}
  def eval({:app, f, a}, env), do: apply(eval(f, env), eval(a, env))

  def eval({:data, name, params, indices}, env),
    do: {:vdata, name, Enum.map(params ++ indices, &eval(&1, env))}

  def eval({:ctor, name, args}, env), do: {:vctor, name, Enum.map(args, &eval(&1, env))}

  # Primitive Int: literals and arithmetic. `{:prim, op, args}` folds when every
  # argument reduces to a literal; otherwise it stays neutral so open terms
  # (`n + 1`) read back and compare structurally.
  def eval({:int_type}, _env), do: {:vint_type}
  def eval({:int_lit, n}, _env), do: {:vint, n}
  def eval({:float_type}, _env), do: {:vfloat_type}
  def eval({:float_lit, f}, _env), do: {:vfloat, f}
  def eval({:prim, op, args}, env), do: prim(op, Enum.map(args, &eval(&1, env)))

  # Opaque until the global is certified total (M7 gates δ here).
  def eval({:global, name}, _env), do: {:vneutral, {:nglobal, name}}


  # `rewrite e at (x.M) in t` is erased at runtime to `t` (the proof and motive
  # are computationally irrelevant — `rewrite e _ t ⇝ t`, §4.6).

  def eval({:case, scrut, motive, branches}, env) do
    case eval(scrut, env) do
      {:vctor, cname, args} ->
        {_cname, _arity, body} = Enum.find(branches, fn {c, _ar, _b} -> c == cname end)
        # The branch body binds the constructor's arguments; the last argument is
        # de Bruijn index 0, so the body's environment is reverse(args) ++ env.
        eval(body, Enum.reverse(args) ++ env)

      {:vneutral, neutral} ->
        motive_closure = {:closure, env, motive}
        branch_closures = Enum.map(branches, fn {c, ar, b} -> {c, ar, {:closure, env, b}} end)
        {:vneutral, {:ncase, neutral, motive_closure, branch_closures}}
    end
  end

  @doc """
  Apply a function value to an argument value, performing β-reduction.

  A `:vlam` reduces by evaluating its body in the captured environment extended
  with the argument; a neutral function accumulates the argument on its spine.
  """
  @spec apply(Cure.Core.Value.t(), Cure.Core.Value.t()) :: Cure.Core.Value.t()
  def apply({:vlam, _dom, {:closure, env, body}}, varg), do: eval(body, [varg | env])
  def apply({:vneutral, n}, varg), do: {:vneutral, {:napp, n, varg}}

  @doc """
  Instantiate a closure (e.g. a Π/Σ codomain family) at a value: evaluate the
  closure body in its captured environment extended with `value` at index 0.
  """
  @spec apply_closure({:closure, [Cure.Core.Value.t()], Cure.Core.Term.t()}, Cure.Core.Value.t()) ::
          Cure.Core.Value.t()
  def apply_closure({:closure, env, body}, value), do: eval(body, [value | env])

  # -- projection ι -----------------------------------------------------------

  # Fold a primitive when its arguments are concrete literals; a failed fold
  # (e.g. division by zero) or a non-literal argument leaves the op stuck.
  defp prim(op, args) do
    case fold(op, args) do
      {:ok, value} -> value
      :stuck -> {:vneutral, {:nprim, op, args}}
    end
  end

  defp fold(:add, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a + b}}
  defp fold(:sub, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a - b}}
  defp fold(:mul, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a * b}}
  defp fold(:div, [{:vint, _}, {:vint, 0}]), do: :stuck
  defp fold(:div, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, div(a, b)}}
  defp fold(:rem, [{:vint, _}, {:vint, 0}]), do: :stuck
  defp fold(:rem, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, rem(a, b)}}

  defp fold(:add, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a + b}}
  defp fold(:sub, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a - b}}
  defp fold(:mul, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a * b}}
  defp fold(:div, [{:vfloat, a}, {:vfloat, b}]) when b != 0.0, do: {:ok, {:vfloat, a / b}}

  # Bool-producing folds now yield the `True`/`False` **constructor values** of the
  # canonical Bool inductive (the True/False ctor values). `:True`/`:False` are
  # hardcoded here (fold has no `sig` on its path — a deliberate plumbing decision;
  # the Task-10 antibody enforces agreement with Builtins.@schemas / seed/1).
  defp fold(:eq, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a == b)}
  defp fold(:eq, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a == b)}
  defp fold(:ne, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a != b)}
  defp fold(:ne, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a != b)}
  defp fold(:lt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a < b)}
  defp fold(:lt, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a < b)}
  defp fold(:le, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a <= b)}
  defp fold(:le, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a <= b)}
  defp fold(:gt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a > b)}
  defp fold(:gt, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a > b)}
  defp fold(:ge, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a >= b)}
  defp fold(:ge, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a >= b)}

  defp fold(:neg, [{:vint, a}]), do: {:ok, {:vint, -a}}
  defp fold(:neg, [{:vfloat, a}]), do: {:ok, {:vfloat, -a}}

  # The Boolean connectives (`and`/`or`/`not`) and Bool-operand equality
  # (`eq`/`ne` on Bool) are NO LONGER primitives: they are ordinary Cure
  # functions in Std.Bool that `case`-eliminate the inductive Bool
  # (`and`/`or`/`not`/`eq`/`ne`). A residual `{:prim, :and/:or/:not}`
  # or Bool-operand `{:prim, :eq/:ne}` — which a well-typed term can no longer
  # contain — falls through to the `:stuck` catch-all below and is rejected by
  # `Kernel.infer` (`{:unknown_prim, _}`). The numeric `:eq`/`:ne` clauses above
  # (on Int/Float) are untouched.
  defp fold(_op, _args), do: :stuck

  defp vbool(true), do: {:vctor, :True, []}
  defp vbool(false), do: {:vctor, :False, []}
end
