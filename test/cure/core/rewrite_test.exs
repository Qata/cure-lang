defmodule Cure.Core.RewriteTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel, Context, Eval}

  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}
  @dcoupled {:ctor, :Dcoupled, []}

  defp env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0), [
      Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])
    ])
  end

  # motive (x.M) = λx. Box(x)
  @motive {:lam, @dec, {:data, :Box, [], [{:var, 0}]}}

  defp box(d), do: Eval.eval({:data, :Box, [], [d]}, [])

  test "rewrite along refl transports and types at M[b/x]" do
    ctx = Context.extend(Context.empty(env()), box(@causal))
    rw = {:rewrite, {:refl, @causal}, @motive, {:var, 0}}
    assert {:ok, {:vdata, :Box, [{:vctor, :Causal, []}]}} = Kernel.infer(ctx, rw)
  end

  test "rewrite erases at runtime to its body" do
    rw = {:rewrite, {:refl, @causal}, @motive, {:var, 0}}
    assert Eval.eval(rw, [{:vneutral, {:nvar, 0}}]) == {:vneutral, {:nvar, 0}}
  end

  test "negative: a body not of type M[a/x] is a :rewrite_premise error" do
    ctx = Context.extend(Context.empty(env()), box(@dcoupled))
    rw = {:rewrite, {:refl, @causal}, @motive, {:var, 0}}
    assert {:error, :rewrite_premise} = Kernel.infer(ctx, rw)
  end
end
