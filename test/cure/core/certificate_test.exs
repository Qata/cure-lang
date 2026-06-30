defmodule Cure.Core.CertificateTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel, Conv}

  @dec {:data, :Dec, [], []}
  @dcoupled {:ctor, :Dcoupled, []}
  @causal {:ctor, :Causal, []}
  @dec_motive {:lam, @dec, @dec}

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
  end

  defp and_type, do: {:pi, @dec, {:pi, @dec, @dec}}

  defp and_body do
    inner = {:case, {:var, 0}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]}

    {:lam, @dec,
     {:lam, @dec,
      {:case, {:var, 1}, @dec_motive, [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, inner}]}}}
  end

  defp and_app(a, b), do: {:app, {:app, {:global, :and}, a}, b}

  test "a structurally-total global certifies and then delta-reduces in conversion" do
    env = Env.add_def(base(), :and, and_type(), and_body())
    assert :ok == Kernel.check_def(env, :and)
    assert {:ok, env2} = Kernel.validate_certificate(env, :and)

    # Before certification: and(Causal,Causal) is stuck (no δ).
    refute Conv.conv?(and_app(@causal, @causal), @causal, [], 0, env)

    # After: δ unfolds the certified def — and(Causal,Causal) ≡ Causal.
    assert Conv.conv?(and_app(@causal, @causal), @causal, [], 0, env2)
    assert Conv.conv?(and_app(@causal, @dcoupled), @dcoupled, [], 0, env2)
    refute Conv.conv?(and_app(@causal, @dcoupled), @causal, [], 0, env2)
  end

  test "a non-terminating global is rejected and stays opaque to δ" do
    env = Env.add_def(base(), :loop, @dec, {:global, :loop})
    assert {:error, :not_total} = Kernel.validate_certificate(env, :loop)
    refute Conv.conv?({:global, :loop}, @causal, [], 0, env)
  end
end
