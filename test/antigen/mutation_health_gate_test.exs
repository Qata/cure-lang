defmodule Antigen.MutationHealthGateTest do
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Generators.Mutation}
  alias Antigen.Backend.StreamData, as: B

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "registry maps mutation/rejection to the mutation assay" do
    assert Runner.assay_module_for("mutation/rejection") == Antigen.Assays.Mutation
  end

  test "mutation_metrics reports diversity ≥ 5, 0 survivors, and stamps healthy" do
    cs = sample(Mutation.mutant(), 200)
    m = Runner.mutation_metrics(cs)
    assert m.mutants_total == 200
    assert m.survivors == 0
    assert m.reason_diversity >= 5
    assert Runner.mutation_stamp(m) == :healthy
  end

  test ":mutant_term challenges are excluded from the :typed_term health gate" do
    cs = sample(Mutation.mutant(), 30)
    # health_metrics filters :typed_term only ⇒ no mutant terms counted
    hm = Runner.health_metrics(cs)
    assert hm.binder_usage == 1.0   # safe_ratio(0,0) ⇒ 1.0 (empty :typed_term subset)
    assert hm.reduction_activity == 1.0
    assert hm.fuel_exhausted_count == 0
  end
end
