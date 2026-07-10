defmodule Antigen.InductiveEnvCoverageTest do
  @moduledoc """
  Red-green coverage proof for the Env-accessor cold-line bucket in
  `lib/cure/core/inductive.ex` (`family?/2`, `register_builtin/3`,
  `ctor_result_indices/2`, `arg_telescope/2`, `field_count/2`,
  `ctor_quantities/2`, `index_telescope/2`, `param_telescope/2`,
  `ctor_result_params/2`): before `Antigen.Generators.InductiveEnv` +
  `Antigen.Assays.InductiveEnv` existed, nothing in the campaign ever declared
  a family through `Inductive.declare/3` and read its metadata back through
  these accessors (every other family-shaped generator/assay either
  hand-destructures the `family`/`ctor` maps directly or never calls
  `register_builtin/3` more than once) — this test proves, via a real
  `:cover`-instrumented run of the actual campaign dispatch path
  (`Antigen.Runner.replay_one/1`, the same `assay_module/1` lookup `mix
  antigen`/replay use), that they now do.

  `async: false`: `:cover` is node-wide global (mirrors `Antigen.CoverTest`).
  """
  use ExUnit.Case, async: false
  alias Antigen.{Cover, Runner, Generators}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.Inductive

  # The exact cold lines this task targets, one entry per accessor function
  # (docstring/task-bucket order matches `lib/cure/core/inductive.ex`).
  @target_lines %{
    "family?/2" => [252],
    "register_builtin/3" => [180, 182, 185],
    "ctor_result_indices/2" => [269, 270, 271],
    "arg_telescope/2" => [279],
    "field_count/2" => [294],
    "ctor_quantities/2" => [301, 302, 303, 304],
    "index_telescope/2" => [311, 312, 313],
    "param_telescope/2" => [321],
    "ctor_result_params/2" => [333, 334, 335, 336]
  }

  test "the inductive/env_roundtrip campaign path covers every targeted Env-accessor cold line" do
    all_targets = @target_lines |> Map.values() |> List.flatten() |> Enum.sort()

    cov =
      Cover.with_cover([Inductive], fn ->
        challenges = B.interp(Generators.InductiveEnv.gen()) |> Enum.take(30)

        # Drive every challenge through the REAL registered dispatch (the same
        # `assay_module/1` lookup `mix antigen`/`Runner.replay/2` use) — not a
        # hand-called `Antigen.Assays.InductiveEnv.run/1` — so this proves the
        # campaign path reaches the accessors, not just the assay module in
        # isolation.
        for c <- challenges do
          assert Runner.replay_one(c) == :ok,
                 "inductive/env_roundtrip rejected a generator-produced challenge: #{inspect(c.payload)}"
        end

        Cover.line_coverage(Inductive)
      end)

    still_cold = all_targets -- cov.covered

    assert still_cold == [],
           "still cold after the campaign: #{inspect(still_cold)} " <>
             "(target lines by function: #{inspect(@target_lines)})"

    # Per-function detail (not just the flattened union) — a stronger guard than
    # the single flat check above, so a future refactor that shifts one
    # function's lines while leaving another's cold fails on the RIGHT function.
    for {fun, lines} <- @target_lines do
      missing = lines -- cov.covered
      assert missing == [], "#{fun}: still cold #{inspect(missing)}"
    end
  end
end
