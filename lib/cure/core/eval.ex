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
  def eval({:sigma, a, b}, env), do: {:vsigma, eval(a, env), {:closure, env, b}}
  def eval({:app, f, a}, env), do: apply(eval(f, env), eval(a, env))
  def eval({:pair, a, b}, env), do: {:vpair, eval(a, env), eval(b, env)}
  def eval({:fst, p}, env), do: vfst(eval(p, env))
  def eval({:snd, p}, env), do: vsnd(eval(p, env))

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

  def eval({:eq, ty, a, b}, env), do: {:veq, eval(ty, env), eval(a, env), eval(b, env)}
  def eval({:refl, a}, env), do: {:vrefl, eval(a, env)}

  # `rewrite e at (x.M) in t` is erased at runtime to `t` (the proof and motive
  # are computationally irrelevant — `rewrite e _ t ⇝ t`, §4.6).
  def eval({:rewrite, _proof, _motive, body}, env), do: eval(body, env)

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

  # Connectives and Bool-operand equality take constructor-value operands now
  # (constructor values). `as_bool/1` maps a True/False ctor value back to an
  # Elixir boolean; a neutral operand → :stuck → prim/2's neutral path.
  defp fold(:and, [a, b]) do
    with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x and y)}
  end

  defp fold(:or, [a, b]) do
    with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x or y)}
  end

  defp fold(:not, [a]) do
    with {:ok, x} <- as_bool(a), do: {:ok, vbool(not x)}
  end

  # Bool-operand equality (`a == b` where a, b : Bool). MUST come after the
  # numeric :eq/:ne clauses above — `[a, b]` matches any 2-tuple list and would
  # otherwise shadow them.
  defp fold(:eq, [a, b]) do
    with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x == y)}
  end

  defp fold(:ne, [a, b]) do
    with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x != y)}
  end

  defp fold(_op, _args), do: :stuck

  defp vbool(true), do: {:vctor, :True, []}
  defp vbool(false), do: {:vctor, :False, []}

  defp as_bool({:vctor, :True, []}), do: {:ok, true}
  defp as_bool({:vctor, :False, []}), do: {:ok, false}
  defp as_bool(_other), do: :stuck

  defp vfst({:vpair, a, _b}), do: a
  defp vfst({:vneutral, n}), do: {:vneutral, {:nfst, n}}

  defp vsnd({:vpair, _a, b}), do: b
  defp vsnd({:vneutral, n}), do: {:vneutral, {:nsnd, n}}
end
