defmodule Antigen.Generators.DeltaReduceFuelCoverTest do
  use ExUnit.Case, async: false
  alias Antigen.Generators.DeltaReduce
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Assays, Cover}
  alias Cure.Core.Normalise

  # The exact cold lines this vertical was built to reach (Normalise fuel/opts
  # plumbing + certified-δ unfolding tail — the campaign hard-plateaued at
  # 90.2% kernel coverage with these permanently cold). Proves the CAMPAIGN
  # (generator through its registered assay, under real :cover instrumentation)
  # reaches every one of them — not just that hand-written code paths exist.
  @target_lines [
    # with_fuel/2 — the fuel-exhausted catch clause
    81,
    # fuel_key/0 — the public accessor (read back after run to confirm cleanup)
    89,
    # normalize_opts/1 — the four validation-error raise sites
    112,
    116,
    120,
    126,
    # spend_fuel/1 — the 0 -> throw exhaustion arm
    365,
    # reduce_unfolded/3 — post-unfold ncase branch-miss freeze
    304,
    # unfold_certified_head/3 — direct ncase branch-miss freeze
    263,
    # builtin_op_fold/4 — struct_eq/struct_ne literal fold + arity-mismatch stuck
    333,
    335,
    336,
    355
  ]

  test "the fuel/opts/certified-delta campaign covers every previously-cold Normalise line" do
    coverage =
      Cover.with_cover([Normalise], fn ->
        for %Antigen.Challenge{} = c <- B.interp(DeltaReduce.gen()) |> Enum.take(400) do
          Assays.DeltaReduce.run(c)
        end

        Cover.line_coverage(Normalise)
      end)

    still_cold = @target_lines -- coverage.covered

    assert still_cold == [],
           "target lines still cold after the campaign: #{inspect(still_cold)} " <>
             "(covered: #{inspect(Enum.sort(coverage.covered))})"
  end
end
