defmodule Antigen.Generators.Term do
  @moduledoc """
  The dependent Core term generator (spec §6). Mode-directed inversion of the
  kernel's bidirectional rules; every semantic side-condition is discharged by
  the kernel's own fuel-bounded conversion (`@gen_fuel`). A canonical-inhabitant
  fallback (`SigMenu.canon/2`) makes generation total — at size 0 or an empty
  option set the generator emits the canonical term (spec §6.4).
  """
  alias Antigen.Gen
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Context, Eval, Normalise}

  @gen_fuel 500
  def gen_fuel, do: @gen_fuel

  @spec gen_term(Context.t(), Cure.Core.Term.t()) :: Gen.t()
  def gen_term(ctx, goal), do: Gen.sized(fn size -> gen(ctx, goal, size) end)

  # size 0 → canonical inhabitant (total, no search).
  defp gen(ctx, goal, 0), do: Gen.return(SigMenu.canon(ctx, goal))

  defp gen(ctx, goal, size) do
    wgoal = whnf(ctx, goal)
    rules = intro_rules(ctx, goal, wgoal, size)

    case rules do
      [] -> Gen.return(SigMenu.canon(ctx, goal))
      rs -> Gen.frequency([{1, Gen.return(SigMenu.canon(ctx, goal))} | rs])
    end
  end

  # -- check-mode introductions ----------------------------------------------
  defp intro_rules(ctx, _goal, {:pi, dom, cod}, size) do
    body_ctx = Context.extend(ctx, Eval.eval(dom, Context.env(ctx)))
    [{3, Gen.bind(gen(body_ctx, cod, size - 1), fn b -> Gen.return({:lam, dom, b}) end)}]
  end

  defp intro_rules(ctx, _goal, {:sigma, a, b}, size) do
    [{3,
      Gen.bind(gen(ctx, a, size - 1), fn av ->
        # `b` is written one binder deeper than `ctx` (sigma binds in `b`); the
        # component that ends up inside `{:pair, av, bv}` must be a term in the
        # UNEXTENDED `ctx` (`Kernel.check`'s `:pair` clause checks it there) —
        # so β-substitute `av` for `b`'s own bound variable via `SigMenu.subst0/3`
        # (same reasoning as `SigMenu.canon`'s Sigma clause, Task 1) before
        # recursing. Unreachable in v1 (see Task 1's note) but must stay correct.
        Gen.bind(gen(ctx, SigMenu.subst0(b, av, ctx), size - 1), fn bv ->
          Gen.return({:pair, av, bv})
        end)
      end)}]
  end

  # The kernel's reified data normal form places Vec's sole (index) argument in
  # the *params* slot with an empty *indices* slot (see SigMenu.vec_index/2), so
  # match position-agnostically over `params ++ indices`.
  defp intro_rules(ctx, _goal, {:data, :Vec, p, idx}, size) do
    [i] = p ++ idx
    ctor_rules_for_vec(ctx, i, size)
  end

  defp intro_rules(_ctx, _goal, {:data, :Nat, _, _}, size) do
    [
      {2, Gen.return({:ctor, :Z, []})},
      {2, Gen.bind(gen_nat(size - 1), fn n -> Gen.return(n) end)}
    ]
  end

  defp intro_rules(_ctx, _goal, {:data, :Bd, _, _}, _size) do
    [{2, Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}])}]
  end

  defp intro_rules(_ctx, _goal, {:type, _}, _size) do
    [{2, Gen.member_of([SigMenu.nat(), SigMenu.bd(), SigMenu.vec({:ctor, :Z, []})])}]
  end

  defp intro_rules(_ctx, _goal, _other, _size), do: []

  # Constructor choice under indices (spec §6.3): vnil iff i≡Z, vcons iff i≡S(j).
  defp ctor_rules_for_vec(ctx, i, size) do
    case whnf(ctx, i) do
      {:ctor, :Z, []} ->
        [{2, Gen.return({:ctor, :vnil, []})}]

      {:ctor, :S, [j]} ->
        if SigMenu.inhabitable?(ctx, SigMenu.vec(j)) do
          [{2,
            Gen.bind(gen(ctx, SigMenu.nat(), size - 1), fn x ->
              Gen.bind(gen(ctx, SigMenu.vec(j), size - 1), fn tail ->
                Gen.return({:ctor, :vcons, [j, x, tail]})
              end)
            end)}]
        else
          []
        end

      _stuck ->
        []   # stuck index: only eliminations apply (Task 4); intros offer nothing
    end
  end

  # A small closed Nat generator (numerals), for variety at Nat goals.
  defp gen_nat(0), do: Gen.return({:ctor, :Z, []})
  defp gen_nat(size) do
    Gen.frequency([
      {2, Gen.return({:ctor, :Z, []})},
      {2, Gen.bind(gen_nat(size - 1), fn n -> Gen.return({:ctor, :S, [n]}) end)}
    ])
  end

  # whnf that degrades to the input term on fuel exhaustion (never crashes gen).
  # Bounded by @gen_fuel, not the default :infinity — spec §6.3: the shape/
  # index inspections this backs ("is the goal a Pi/data/Vec(S j)?") are
  # semantic conditions and must run under the same @gen_fuel-bounded kernel
  # calls as the acceptance rule, "not a separate unbounded check".
  defp whnf(ctx, term) do
    case Normalise.whnf(ctx, term, fuel: @gen_fuel) do
      :fuel_exhausted -> term
      w -> w
    end
  end
end
