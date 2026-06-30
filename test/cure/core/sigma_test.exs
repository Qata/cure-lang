defmodule Cure.Core.SigmaTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel, Context, Eval, Conv}

  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}

  defp build_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0), [
      Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])
    ])
  end

  # Σ(d:Dec). Box(d)
  @sigma {:sigma, @dec, {:data, :Box, [], [{:var, 0}]}}

  test "Sigma formation is a type at the max level" do
    assert {:ok, {:vtype, 0}} == Kernel.infer(Context.empty(build_env()), @sigma)
  end

  test "checks a dependent pair against its Sigma type" do
    e = build_env()
    # ctx: bx : Box(Causal)
    ctx = Context.extend(Context.empty(e), Eval.eval({:data, :Box, [], [@causal]}, []))
    sigma_val = Eval.eval(@sigma, Context.env(ctx))
    pair = {:pair, @causal, {:var, 0}}
    assert :ok == Kernel.check(ctx, pair, sigma_val)
  end

  test "snd substitutes (fst p) into the second component's type" do
    e = build_env()
    ctx = Context.extend(Context.empty(e), Eval.eval(@sigma, []))
    # p = var 0 : Σ(d:Dec). Box(d). snd p : Box(fst p), fst p stuck (neutral).
    assert {:ok, {:vdata, :Box, [{:vneutral, {:nfst, {:nvar, 0}}}]}} =
             Kernel.infer(ctx, {:snd, {:var, 0}})

    assert {:ok, {:vdata, :Dec, []}} == Kernel.infer(ctx, {:fst, {:var, 0}})
  end

  test "negative: a second component of the wrong type is a :sigma_mismatch" do
    e = build_env()
    ctx = Context.empty(e)
    sigma_val = Eval.eval(@sigma, [])
    # (Causal, Dcoupled): Dcoupled : Dec, but Box(Causal) is expected
    pair = {:pair, @causal, {:ctor, :Dcoupled, []}}
    assert {:error, :sigma_mismatch} = Kernel.check(ctx, pair, sigma_val)
  end

  test "iota: both projection rules hold definitionally" do
    pair = {:pair, {:type, 0}, {:type, 1}}
    assert Conv.conv?({:fst, pair}, {:type, 0}, [], 0)
    assert Conv.conv?({:snd, pair}, {:type, 1}, [], 0)
  end
end
