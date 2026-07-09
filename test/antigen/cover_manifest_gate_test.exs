defmodule Antigen.CoverManifestGateTest do
  @moduledoc """
  The Antigen shape-coverage gate (design
  `docs/superpowers/specs/2026-07-10-antigen-coverage-manifest-design.md`).

  Fails when a declared coverage cell is never produced (the recurrence-preventing
  check — a declared-but-unhit cell is exactly what each of the four second-pass
  findings was), and when a registered assay is neither sampled from the explorer
  pool nor an acknowledged curated vertical (dead / unwired assay).
  """
  use ExUnit.Case, async: true
  alias Antigen.{CoverManifest, Runner}
  alias Antigen.Backend.StreamData, as: B

  # Registered assays fed by seed tests / dedicated harnesses rather than the
  # explorer pool (`Mix.Tasks.Antigen.default_gen/0`). Exempt from the "produced by
  # sampling default_gen" dead-assay check — but still real, running verticals. A
  # registered assay that is neither sampled NOR listed here is genuinely unwired.
  @curated_assays MapSet.new([
                    "stub",
                    "indexed/case",
                    "rewrite/eq",
                    "stuck_elim_delta",
                    "term/erasure_preservation",
                    "elab/completeness",
                    "elab/metamorphic",
                    "elab/erasure",
                    "elab/dot_forcing",
                    "elab/guard_lint",
                    "elab/nat_rep",
                    "elab/soundness",
                    "normalizer/differential",
                    "normalizer/equal",
                    "normalizer/intrinsic",
                    "unify/soundness",
                    "unify/intrinsic",
                    "unify_types/fixpoint",
                    "unify_types/intrinsic",
                    "totality_closure/soundness",
                    "totality_closure/completeness",
                    "erasure/idempotent",
                    "erasure/selective",
                    "erasure/wellformed",
                    "relevance/soundness"
                  ])

  test "every declared shape cell is actually produced (recurrence guard)" do
    missing = CoverManifest.missing(800)

    assert MapSet.size(missing) == 0,
           "coverage-manifest cells never produced: #{inspect(Enum.sort(missing))}"
  end

  test "the four second-pass finding cells are in the manifest" do
    expected = CoverManifest.expected()

    for point <- [
          {"positivity", :app_head_negative},
          {"branchunify/verdict", :param_solved},
          {"universes", :family_ceiling},
          {"totality/diverging", :pending_sibling}
        ] do
      assert MapSet.member?(expected, point), "manifest is missing the finding cell #{inspect(point)}"
    end
  end

  test "the gate DISCRIMINATES: a declared cell with no producing draw is reported" do
    # Synthetic manifest with a cell no participant ever tags → must surface as missing.
    expected = MapSet.put(CoverManifest.expected(), {"positivity", :__never_generated__})
    missing = MapSet.difference(expected, CoverManifest.hit_points(800))

    assert MapSet.member?(missing, {"positivity", :__never_generated__}),
           "gate diff failed to flag a genuinely-unproduced cell"
  end

  test "every registered assay is either sampled from the explorer pool or curated" do
    sampled =
      B.interp(Mix.Tasks.Antigen.default_gen())
      |> Enum.take(6000)
      |> Enum.map(& &1.assay)
      |> MapSet.new()

    unwired =
      Runner.registered_assays()
      |> Enum.reject(fn a -> MapSet.member?(sampled, a) or MapSet.member?(@curated_assays, a) end)

    assert unwired == [],
           "registered assays neither sampled nor curated (unwired?): #{inspect(unwired)}"
  end

  test "every participant declares cells and a sampleable gen/0" do
    for mod <- CoverManifest.participants() do
      assert is_list(mod.cover_cells()) and mod.cover_cells() != []
      assert match?([_ | _], B.interp(mod.gen()) |> Enum.take(1))
    end
  end
end
