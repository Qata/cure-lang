defmodule Antigen.Generators.SigMenu do
  @moduledoc """
  The fixed, versioned Tier-B signature menu (spec §5). Families + certified
  defs the term generator draws goals and heads from, plus the totality
  scaffolding (`inhabitable?/2` + `canon/2`) that makes `gen_term` total.

  Certification runs the REAL procedure (`Kernel.validate_certificate/2`) — never
  a raw `Env.certify/2` bypass (locked decision #3/#5).
  """
  alias Cure.Core.{Env, Inductive, Kernel, Context, Eval}

  # -- goal-type constructors -------------------------------------------------
  def nat, do: {:data, :Nat, [], []}
  def bd, do: {:data, :Bd, [], []}
  def vec(index_term), do: {:data, :Vec, [], [index_term]}
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}

  @doc "The fixed closed goal-type seeds (all inhabitable in the empty context)."
  def goal_types, do: [nat(), bd(), vec(z()), vec(s(z()))]

  # -- the v1 environment -----------------------------------------------------
  @doc "Declare families, add plus/dbl, and certify them through the kernel."
  @spec env_of(:v1) :: Env.t()
  def env_of(:v1) do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Nat, [], [], 0),
        [Inductive.ctor(:Z, [], []), Inductive.ctor(:S, [{:n, nat()}], [])])
      |> Inductive.declare(Inductive.family(:Bd, [], [], 0),
        [Inductive.ctor(:T, [], []), Inductive.ctor(:F, [], [])])
      |> Inductive.declare(Inductive.family(:Vec, [], [{:n, nat()}], 0),
        [
          Inductive.ctor(:vnil, [], [z()]),
          # vcons : (n:Nat) -> Nat -> Vec(n) -> Vec(S(n))
          #   arg telescope [n, x, xs]; in xs's type Vec(n), n is index 1;
          #   in the result index S(n), n is index 2.
          Inductive.ctor(:vcons, [{:n, nat()}, {:x, nat()}, {:xs, vec({:var, 1})}], [s({:var, 2})])
        ])
      |> Inductive.declare(Inductive.family(:List, [{:A, {:type, 0}}], [], 0),
        [
          # Nil : List(A). result_params = [{:var,0}]: with 0 ctor args bound, the
          # family param A sits at var 0 in the checking frame — required so
          # Kernel.check's {:ctor,...} clause re-derives {:vdata,:List,[A]} (not
          # {:vdata,:List,[]}) and converts against the expected List(A).
          Inductive.ctor(:Nil, [], [], [], [{:var, 0}]),
          # Cons : (A) => A -> List(A) -> List(A). In hd's type A is {:var,0} (no
          # ctor args bound yet); in tl's type List(A), A is {:var,1} (hd bound,
          # shifting A down one). result_params = [{:var,2}]: with both args bound
          # (hd, tl), A sits at var 2. Convention confirmed against
          # elab_soundness_test's F(a)/Mk(x:a) and check_uniform_params.
          Inductive.ctor(:Cons, [{:hd, {:var, 0}}, {:tl, {:data, :List, [{:var, 1}], []}}], [],
            [:present, :present], [{:var, 2}])
        ])

    # plus m n = case m of Z -> n | S(k) -> S(plus(k, n))   (structural on arg 1)
    plus_type = {:pi, nat(), {:pi, nat(), nat()}}
    plus_body =
      {:lam, nat(), {:lam, nat(),
        {:case, {:var, 1}, {:lam, nat(), nat()},
         [{:Z, 0, {:var, 0}},
          {:S, 1, s({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}]}}}

    # dbl m = plus m m
    dbl_type = {:pi, nat(), nat()}
    dbl_body = {:lam, nat(), {:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 0}}}

    env = Env.add_def(env, :plus, plus_type, plus_body)
    {:ok, env} = Kernel.validate_certificate(env, :plus)
    env = Env.add_def(env, :dbl, dbl_type, dbl_body)
    {:ok, env} = Kernel.validate_certificate(env, :dbl)
    env
  end

  # -- context rebuild (spec §4.1) --------------------------------------------
  @doc "Rebuild a Context from a kernel-order ctx list (index 0 = innermost)."
  @spec rebuild_context(Env.t(), [Cure.Core.Term.t()]) :: Context.t()
  def rebuild_context(env, ctx_types) do
    Enum.reduce(Enum.reverse(ctx_types), Context.empty(env), fn ty_term, ctx ->
      Context.extend(ctx, Eval.eval(ty_term, Context.env(ctx)))
    end)
  end

  # -- inhabitability + canonical inhabitants (spec §6.4) ---------------------
  @spec inhabitable?(Context.t(), Cure.Core.Term.t()) :: boolean()
  def inhabitable?(ctx, goal) do
    case whnf(ctx, goal) do
      {:data, :Nat, _, _} -> true
      {:data, :Bd, _, _} -> true
      {:type, _} -> true
      {:pi, dom, cod} -> inhabitable?(Context.extend(ctx, Eval.eval(dom, Context.env(ctx))), cod)
      {:sigma, a, b} ->
        inhabitable?(ctx, a) and
          inhabitable?(Context.extend(ctx, Eval.eval(a, Context.env(ctx))), b)
      {:data, :Vec, p, idx} ->
        i = vec_index(p, idx)
        closed_numeral?(whnf(ctx, i)) or has_var_of_type?(ctx, vec(i))
      {:data, :List, [a], _} -> inhabitable?(ctx, a)
      _ -> false
    end
  end

  @spec canon(Context.t(), Cure.Core.Term.t()) :: Cure.Core.Term.t()
  def canon(ctx, goal) do
    case whnf(ctx, goal) do
      {:data, :Nat, _, _} -> z()
      {:data, :Bd, _, _} -> {:ctor, :T, []}
      {:type, _} -> nat()
      {:pi, dom, cod} ->
        {:lam, dom, canon(Context.extend(ctx, Eval.eval(dom, Context.env(ctx))), cod)}
      {:sigma, a, b} ->
        av = canon(ctx, a)
        {:pair, av, canon(ctx, subst0(b, av, ctx))}
      {:data, :Vec, p, idx} ->
        i = vec_index(p, idx)
        case whnf(ctx, i) do
          {:ctor, :Z, []} -> {:ctor, :vnil, []}
          {:ctor, :S, [j]} -> {:ctor, :vcons, [j, z(), canon(ctx, vec(j))]}
          _ -> var_of_type(ctx, vec(i))   # stuck index: a Γ-var by the invariant
        end
      {:data, :List, [_a], _} -> {:ctor, :Nil, []}
    end
  end

  # The Vec family has zero parameters and one index; the kernel's reified data
  # normal form (`Quote.reify` of `{:vdata, :Vec, args}`) places that single arg
  # in the *params* slot with an empty *indices* slot, while a freshly built
  # `vec/1` term puts it in *indices* — so read the index position-agnostically
  # from `params ++ indices` (exactly one element either way).
  defp vec_index(params, indices) do
    [i] = params ++ indices
    i
  end

  # -- helpers ----------------------------------------------------------------
  # Deliberately unbounded (unlike Generators.Term's own `whnf/2`, which spec
  # §6.3 requires to run under @gen_fuel): this helper backs the totality
  # FALLBACK (`inhabitable?`/`canon`), not a generator choice being accepted
  # or rejected against a goal — it is not one of the "semantic conditions"
  # locked decision #3 scopes. `canon/2`'s job is to always terminate with an
  # answer given v1's finite, closed menu, and threading a fuel budget through
  # here would change `inhabitable?/2`/`canon/2`'s public 2-arity (used
  # throughout Tasks 1/3/4/6/7/8/9) for no v1 behavioral benefit.
  defp whnf(ctx, term) do
    case Cure.Core.Normalise.whnf(ctx, term) do
      :fuel_exhausted -> term
      w -> w
    end
  end

  defp closed_numeral?({:ctor, :Z, []}), do: true
  defp closed_numeral?({:ctor, :S, [n]}), do: closed_numeral?(n)
  defp closed_numeral?(_), do: false

  # Does Γ hold a variable whose type converts with `goal`?
  defp has_var_of_type?(ctx, goal), do: var_of_type(ctx, goal) != nil

  defp var_of_type(ctx, goal) do
    env = Context.env(ctx)
    depth = Context.length(ctx)
    sig = Context.signature(ctx)

    Enum.find_value(0..(depth - 1)//1, fn k ->
      ty_val = Context.lookup(ctx, k)
      ty_term = Cure.Core.Normalise.quote(ty_val, depth)

      case Cure.Core.Conv.conv_within?(ty_term, goal, env, depth, sig, 500) do
        {:ok, true} -> {:var, k}
        _ -> nil
      end
    end)
  end

  # β-substitute `arg`'s value for the Sigma's own bound variable (de Bruijn 0)
  # into `b`. `b` is written one binder deeper than `ctx` (the `:sigma` binding
  # convention: `{:sigma, a, b}` binds in `b`, matching `Kernel.infer`'s
  # `ctx2 = Context.extend(ctx, a_value)` before checking `b`) — but the
  # component actually placed in `{:pair, av, ...}` must be a term in the
  # UNEXTENDED `ctx` (`Kernel.check`'s `:pair` clause checks its second
  # component in the original `ctx`, against `cod_closure` applied to
  # `a_value` — never in an extended context). A raw `Term.subst/3` is not
  # enough: it replaces only index 0 and leaves every OTHER free index in `b`
  # unchanged, so a reference to an outer `ctx` variable would stay off-by-one.
  # Evaluating `b` under `[arg_value | env]` and quoting back (the same
  # technique `subst_cod` in Task 4 uses) performs the substitution and the
  # necessary renumbering in one step.
  @spec subst0(Cure.Core.Term.t(), Cure.Core.Term.t(), Context.t()) :: Cure.Core.Term.t()
  def subst0(b, arg, ctx) do
    env = Context.env(ctx)
    arg_value = Eval.eval(arg, env)
    Cure.Core.Normalise.quote(Eval.eval(b, [arg_value | env]), Context.length(ctx))
  end
end
