defmodule Antigen.ConvNatBridgeCoverageTest do
  @moduledoc """
  Red-green coverage proof for the compact-Nat conversion bridge in
  `lib/cure/core/conv.ex` — the definitional-equality clauses between a compact
  `{:vnat, n}` literal and its n-fold S/Z tower (`conv_struct?` 85/88/91) and the
  neutral-spine no-δ fast path on a nat-literal argument (`same_value_no_delta?`
  194), plus the structurally-distinct stuck-neutral head-mismatch fallback
  (`conv_neutral?` 146). These are the conversion-layer sibling of the audited
  compact-lit↔tower unifier bridge; before the `ConvPair` generator's compact-Nat
  shapes existed, no generator drove two `{:vnat,_}` values (or a literal vs a
  tower) into `conv?`, so the whole bridge sat cold.

  Drives the REAL campaign dispatch (`Runner.replay_one/1`); `async: false` because
  `:cover` is node-wide global.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Cover, Runner, Generators}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.Conv

  @target_lines [85, 88, 91, 146, 194]

  test "the conv/decision campaign path warms the compact-Nat bridge cold lines" do
    cov =
      Cover.with_cover([Conv], fn ->
        challenges = B.interp(Generators.ConvPair.gen()) |> Enum.take(600)

        for c <- challenges do
          assert Runner.replay_one(c) == :ok,
                 "conv/decision misjudged a generator-produced pair: #{inspect(c.payload)}"
        end

        Cover.line_coverage(Conv)
      end)

    still_cold = @target_lines -- cov.covered

    assert still_cold == [],
           "compact-Nat bridge still cold after the conv/decision campaign: #{inspect(still_cold)}"
  end
end
