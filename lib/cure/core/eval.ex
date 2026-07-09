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

  # Primitive Int/Float literals. Arithmetic is builtin-op GLOBALS (K2, spec
  # 2026-07-09): Eval leaves every global neutral; the certified-δ engine
  # (Normalise) folds saturated literal spines via `fold/2` below.
  def eval({:int_type}, _env), do: {:vint_type}
  def eval({:int_lit, n}, _env), do: {:vint, n}

  # Compact Nat literal: a machine integer standing for the n-fold `S`-tower over
  # `Z` (Lean kernel Nat / Agda BUILTIN NATURAL). It never materializes the tower;
  # `nat_to_ctor/1` peels one layer on demand at each ι-site.
  def eval({:nat_lit, n}, _env), do: {:vnat, n}
  def eval({:float_type}, _env), do: {:vfloat_type}
  def eval({:float_lit, f}, _env), do: {:vfloat, f}

  # Opaque until the global is certified total (M7 gates δ here).
  def eval({:global, name}, _env), do: {:vneutral, {:nglobal, name}}


  # `rewrite e at (x.M) in t` is erased at runtime to `t` (the proof and motive
  # are computationally irrelevant — `rewrite e _ t ⇝ t`, §4.6).

  def eval({:case, scrut, motive, branches}, env) do
    case eval(scrut, env) do
      {:vctor, cname, args} ->
        {_cname, arity, body} = Enum.find(branches, fn {c, _ar, _b} -> c == cname end)
        # The branch body binds the constructor's FIELDS (arity of them); the last
        # field is de Bruijn index 0, so the body's environment is
        # reverse(fields) ++ env. A K6 params-on-spine ctor value carries family
        # params ahead of its fields — `drop_leading_params` coerces to fields-only.
        fields = drop_leading_params(args, arity)
        eval(body, Enum.reverse(fields) ++ env)

      # A compact Nat scrutinee peels ONE layer to `Z`/`S(pred)` and reuses the
      # ι-rule above (`Z` → the Z-branch in `env`; `S` → the S-branch binding the
      # compact predecessor at index 0). The tail stays compact, so eliminating a
      # depth-n literal is n reduction steps, never an n-node heap tower.
      {:vnat, _} = nat ->
        {:vctor, cname, args} = nat_to_ctor(nat)
        {_cname, arity, body} = Enum.find(branches, fn {c, _ar, _b} -> c == cname end)
        fields = drop_leading_params(args, arity)
        eval(body, Enum.reverse(fields) ++ env)

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

  # -- fields-only ι ----------------------------------------------------------

  # Fields-only canonicalization: a K6 params-on-spine ctor value carries its
  # family params ahead of its fields; the ι-rule binds ONLY the fields (the
  # branch's `arity`). length(args) == arity is the canonical zero-cost path.
  # Public (`@doc false`) so `Cure.Core.Normalise`'s two ι sites call the SAME
  # function (Step 1.3) — a single audited algorithm, not a duplicated twin.
  @doc false
  def drop_leading_params(args, arity) when length(args) > arity,
    do: Enum.drop(args, length(args) - arity)

  def drop_leading_params(args, _arity), do: args

  # -- compact Nat peeling ----------------------------------------------------

  # Peel one layer of a compact Nat literal into its `Z`/`S` constructor value,
  # leaving the predecessor COMPACT (`{:vnat, n-1}`). This is the single audited
  # literal→constructor mapping (Lean's `toCtorIfLit` / Agda's `matchLitSuc`);
  # every ι-site (`eval`'s `:case`, `Normalise`'s two `ncase` arms) routes a
  # `{:vnat, _}` scrutinee through it so the peel logic exists exactly once.
  # Public (`@doc false`) for the Normalise call-sites — same pattern as
  # `drop_leading_params/2`.
  @doc false
  def nat_to_ctor({:vnat, 0}), do: {:vctor, :Z, []}
  def nat_to_ctor({:vnat, n}) when is_integer(n) and n > 0, do: {:vctor, :S, [{:vnat, n - 1}]}

  # Peel iff the value is a compact Nat; otherwise pass through unchanged. Lets a
  # whnf-forced scrutinee be normalised to constructor form before the shared
  # `{:vctor, cname, cargs}` ι-logic without a separate branch.
  @doc false
  def nat_to_ctor_if({:vnat, _} = nat), do: nat_to_ctor(nat)
  def nat_to_ctor_if(value), do: value

  # -- projection ι -----------------------------------------------------------

  # The audited δ fold table. Public (`@doc false`) so `Cure.Core.Normalise`'s
  # builtin-op compute hook folds through the SAME table (K2, spec 2026-07-09).
  # Returns `{:ok, value} | :stuck`; §G.1 rule 1 = div/rem by literal zero stays
  # `:stuck` (the spine stays neutral, never crashes).
  @doc false
  def fold(:add, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a + b}}
  def fold(:sub, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a - b}}
  def fold(:mul, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a * b}}
  def fold(:div, [{:vint, _}, {:vint, 0}]), do: :stuck
  def fold(:div, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, div(a, b)}}
  def fold(:rem, [{:vint, _}, {:vint, 0}]), do: :stuck
  def fold(:rem, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, rem(a, b)}}

  def fold(:add, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a + b}}
  def fold(:sub, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a - b}}
  def fold(:mul, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a * b}}
  def fold(:div, [{:vfloat, a}, {:vfloat, b}]) when b != 0.0, do: {:ok, {:vfloat, a / b}}

  # Bool-producing folds now yield the `True`/`False` **constructor values** of the
  # canonical Bool inductive (the True/False ctor values). `:True`/`:False` are
  # hardcoded here (fold has no `sig` on its path — a deliberate plumbing decision;
  # the Task-10 antibody enforces agreement with Builtins.@schemas / seed/1).
  def fold(:eq, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a == b)}
  def fold(:eq, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a == b)}
  def fold(:ne, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a != b)}
  def fold(:ne, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a != b)}
  def fold(:lt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a < b)}
  def fold(:lt, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a < b)}
  def fold(:le, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a <= b)}
  def fold(:le, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a <= b)}
  def fold(:gt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a > b)}
  def fold(:gt, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a > b)}
  def fold(:ge, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a >= b)}
  def fold(:ge, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a >= b)}

  def fold(:neg, [{:vint, a}]), do: {:ok, {:vint, -a}}
  def fold(:neg, [{:vfloat, a}]), do: {:ok, {:vfloat, -a}}

  # The Boolean connectives (`and`/`or`/`not`) and Bool-operand equality are
  # Std.Bool `case`-defs, never entries in this table. The catch-all is §G.1
  # rule 1's backstop: any op/argument pair with no clause above (zero divisor,
  # non-literal value, Bool ctor operand) is `:stuck` — the builtin-op spine
  # stays neutral, never unsound (K2, spec 2026-07-09).
  def fold(_op, _args), do: :stuck

  defp vbool(true), do: {:vctor, :True, []}
  defp vbool(false), do: {:vctor, :False, []}
end
