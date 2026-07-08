defmodule Cure.Elab.UnifyMetaCompletenessTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{MetaCtx, Unify}
  alias Cure.Core.{Env, Inductive}

  # The metavariable traversals in `Unify` (`zonk`, `meta_free?`, `occurs?`) must
  # recurse into EVERY subterm-bearing Core shape. They previously stopped at
  # `{:data}`/`{:ctor}`/`{:app}`/`{:pi}`/`{:lam}` and treated `{:eq}`/`{:sigma}`/
  # `{:pair}`/`{:fst}`/`{:snd}`/`{:refl}`/`{:prim}` as opaque leaves. A meta buried
  # in one of those then (a) survived `zonk` unsubstituted and (b) slipped past
  # `meta_free?`, so the δ-convertibility fallback handed a `{:meta, _}`-bearing
  # term to the TRUSTED evaluator — `no function clause in Cure.Core.Eval.eval/2`,
  # an elaborator crash of the kernel (seen on a higher-order implicit like
  # `subst({P},{x},{y}, e: Eq(a,x,y), px: P(x))`).

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}

  defp nat_sig do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
  end

  test "zonk substitutes a solution buried in Eq / refl endpoints" do
    ctx = MetaCtx.put_solution(elem(MetaCtx.fresh(MetaCtx.new()), 0), 0, @z)
    t = {:eq, {:meta, 0}, {:meta, 0}, {:refl, {:meta, 0}}}
    assert {:eq, @z, @z, {:refl, @z}} == Unify.zonk(t, ctx)
  end

  test "zonk substitutes a solution buried in Sigma / pair / fst / snd" do
    ctx = MetaCtx.put_solution(elem(MetaCtx.fresh(MetaCtx.new()), 0), 0, @z)

    assert {:sigma, @z, @z} == Unify.zonk({:sigma, {:meta, 0}, {:meta, 0}}, ctx)
    assert {:pair, @z, @z} == Unify.zonk({:pair, {:meta, 0}, {:meta, 0}}, ctx)
    assert {:fst, @z} == Unify.zonk({:fst, {:meta, 0}}, ctx)
    assert {:snd, @z} == Unify.zonk({:snd, {:meta, 0}}, ctx)
  end

  test "unify does not crash the kernel on a metavariable buried in a prim (delta fallback)" do
    # Two distinct `:prim` terms have no structural do_unify clause and fall to
    # the δ-convertibility fallback. One carries an UNSOLVED meta buried inside;
    # `meta_free?` must detect it and refuse the fallback, returning a clean error
    # instead of passing `{:meta, _}` to `Cure.Core.Eval.eval`. (Migrated from
    # the retired primitive `{:eq}` carrier, Phase C — `:prim` is the surviving
    # structural-clause-free shape.)
    {ctx, m} = MetaCtx.fresh(MetaCtx.new())
    t1 = {:prim, :add, [{:meta, m}, {:int_lit, 0}]}
    t2 = {:prim, :add, [{:int_lit, 1}, {:int_lit, 0}]}

    assert {:error, _} = Unify.unify(t1, t2, ctx, nat_sig())
  end
end
