defmodule Cure.Core.EqTest do
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
  end

  test "Eq formation is a type at the level of its carrier" do
    assert {:ok, {:vtype, 0}} ==
             Kernel.infer(Context.empty(env()), {:eq, @dec, @causal, @causal})
  end

  test "refl checks against a reflexive equation" do
    eq = Eval.eval({:eq, @dec, @causal, @causal}, [])
    assert :ok == Kernel.check(Context.empty(env()), {:refl, @causal}, eq)
  end

  test "refl uses real conversion (beta), not name matching" do
    # Eq Dec ((λx:Dec.x) Causal) Causal — endpoints equal only after β.
    lhs = {:app, {:lam, @dec, {:var, 0}}, @causal}
    eq = Eval.eval({:eq, @dec, lhs, @causal}, [])
    assert :ok == Kernel.check(Context.empty(env()), {:refl, @causal}, eq)
  end

  test "negative: refl rejects a non-reflexive equation (the audit bug)" do
    eq = Eval.eval({:eq, @dec, @causal, @dcoupled}, [])
    assert {:error, :not_definitionally_equal} =
             Kernel.check(Context.empty(env()), {:refl, @causal}, eq)
  end

  test "infers refl's type as a reflexive equation" do
    assert {:ok, {:veq, {:vdata, :Dec, []}, {:vctor, :Causal, []}, {:vctor, :Causal, []}}} =
             Kernel.infer(Context.empty(env()), {:refl, @causal})
  end
end
