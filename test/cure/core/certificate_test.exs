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

  test "a mutually-recursive cycle f→g→f is NOT certified (mutual recursion is soundly rejected)" do
    ty = {:pi, @dec, @dec}
    bf = {:lam, @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, @dec, {:app, {:global, :f}, {:var, 0}}}
    env = base() |> Env.add_def(:f, ty, bf) |> Env.add_def(:g, ty, bg)

    assert {:error, :not_total} = Kernel.validate_certificate(env, :f)
    assert {:error, :not_total} = Kernel.validate_certificate(env, :g)
    # ...and neither δ-unfolds in conversion (stays opaque).
    refute Conv.conv?({:app, {:global, :f}, @causal}, @causal, [], 0, env)
  end

  test "a def that calls an unrelated (non-cyclic) global is still certified" do
    # `use_id = λx. id x` where `id = λx. x`: id does not call back, so use_id is
    # not in a cycle and must remain certifiable (guards against over-rejection).
    ty = {:pi, @dec, @dec}
    id_body = {:lam, @dec, {:var, 0}}
    use_body = {:lam, @dec, {:app, {:global, :id}, {:var, 0}}}
    env = base() |> Env.add_def(:id, ty, id_body) |> Env.add_def(:use_id, ty, use_body)

    assert {:ok, _} = Kernel.validate_certificate(env, :use_id)
  end
end
