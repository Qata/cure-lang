defmodule Antigen.Assays.TotalityClosureAssayTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.TotalityClosureAssay, Challenge}
  alias Antigen.Generators.ClosureEnv
  alias Cure.Core.Env

  defp int_arrow, do: {:pi, {:int_type}, {:int_type}}
  defp loop_def(env), do: Env.add_def(env, :loop, int_arrow(), {:lam, {:int_type}, {:app, {:global, :loop}, {:var, 0}}})
  defp total_def(env), do: Env.add_def(env, :total_id, int_arrow(), {:lam, {:int_type}, {:var, 0}})
  defp with_family_index(env, fam, g),
    do: %{env | families: Map.put(env.families, fam, %{name: fam, params: [], indices: [{:i, {:app, {:global, g}, {:int_lit, 0}}}], level: 0})}
  defp with_ctor_index(env, ct, g),
    do: %{env | ctors: Map.put(env.ctors, ct, %{name: ct, args: [], result_indices: [{:app, {:global, g}, {:int_lit, 0}}], result_params: [], quantities: []})}

  defp snd_ch(env, expect) do
    Challenge.new(kind: :closure_env, assay: "totality_closure/soundness", label: :diverging,
      payload: %{env: env, expect: expect}, seed: 1)
  end

  test "reject baseline: diverging :loop in a family index — real certify rejects" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    assert TotalityClosureAssay.run(snd_ch(env, :reject)) == :ok
  end

  test "reject baseline: diverging :loop in a ctor result_indices — real certify rejects" do
    env = Env.empty() |> loop_def() |> with_ctor_index(:Wrap, :loop)
    assert TotalityClosureAssay.run(snd_ch(env, :reject)) == :ok
  end

  test "accept control: an all-total type-level env certifies (rejection is divergence-specific)" do
    env = Env.empty() |> total_def() |> with_family_index(:Vessel, :total_id)
    assert TotalityClosureAssay.run(snd_ch(env, :accept)) == :ok
  end

  test "negative control: an unconditional-{:ok} certify stub certifies the diverger" do
    env = Env.empty() |> loop_def() |> with_family_index(:Vessel, :loop)
    k = %{TotalityClosureAssay.__real__() | certify: fn e -> {:ok, e} end}
    assert {:violation, {:diverging_certified, _}} = TotalityClosureAssay.run(snd_ch(env, :reject), k)
  end

  test "negative control: a certify stub that errors on the all-total env is caught (:accept branch)" do
    # Every violation branch needs a negative control (V2 plan-review lesson).
    # :total_env_not_certified's `other` case is reachable under REAL ops — it is
    # exactly what a malformed accept-control env (spec §8-2(a)) or a driver
    # false-rejection would produce — unlike :unexpected_certify_result (see the
    # note after Step 3), so it gets its own dedicated stub here rather than being
    # exercised only implicitly by the accept-control test passing.
    env = Env.empty() |> total_def() |> with_family_index(:Vessel, :total_id)
    k = %{TotalityClosureAssay.__real__() | certify: fn _e -> {:error, {:totality_required, :total_id}} end}
    assert TotalityClosureAssay.run(snd_ch(env, :accept), k) ==
             {:violation, {:total_env_not_certified, {:error, {:totality_required, :total_id}}}}
  end
end
