defmodule Antigen.KernelProbeCoverageTest do
  @moduledoc """
  Red-green coverage proof for the kernel def-level / sibling-module cold-line
  bucket driven by `Antigen.Generators.KernelProbe` + `Antigen.Assays.KernelProbe`.

  These lines are *defensive* clauses reached through the kernel's def and family
  machinery (`check_def`, `validate_certificate`, `check_family`, `normalize/3`,
  the Final-Core validator-emit fold, `infer`'s `{:absurd}`/fields-only/ctor-arity
  rejections, `remap_index_error`'s non-family passthrough) or the sibling trusted
  modules (`Quote.split_data_args` foreign-family fallback, `Inductive.occurs_deep?`
  through-constructor recursion, `Serialize.sym_atom` un-interned rejection, and
  `Certificate`'s under-application + dangling-callee paths). No term-shaped
  generator reaches them: they are entry points into def/family/certification code,
  not `infer` of a single closed Core term, or inputs the runner's `well_formed?`
  gate discards. This test proves — via a real `:cover` run of the actual campaign
  dispatch path (`Runner.replay_one/1`) — that they now warm.

  `async: false`: `:cover` is node-wide global (mirrors `Antigen.CoverTest`).
  """
  use ExUnit.Case, async: false
  alias Antigen.{Cover, Runner, Generators}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Kernel, Quote, Serialize, Inductive, Certificate, Eval, Conv}

  # Target cold lines, per instrumented module (source order). The trailing block
  # (Eval/Conv + Kernel 377) is the adversarial-backstop set: lines reached only by
  # feeding the kernel malformed input at a real boundary — the ι-guards in
  # `Eval.eval`/`Eval.apply`, `coerce_fields`'s unknown-ctor fallback, and the
  # Final-Core validator's hole-body rejection. See the `:eval_no_branch` … probes.
  @targets %{
    Kernel => [42, 78, 175, 301, 332, 342, 366, 369, 377, 396, 431, 604],
    Quote => [86],
    Serialize => [206],
    Inductive => [425, 426],
    Certificate => [286, 414, 541],
    Eval => [71, 81, 99],
    Conv => [221]
  }

  test "the kernel/probe campaign path warms every targeted def-level cold line" do
    modules = Map.keys(@targets)

    cov =
      Cover.with_cover(modules, fn ->
        # Enough draws to hit every probe of the fixed member_of menu with
        # overwhelming probability (20 probes, 500 draws).
        challenges = B.interp(Generators.KernelProbe.gen()) |> Enum.take(500)

        for c <- challenges do
          assert Runner.replay_one(c) == :ok,
                 "kernel/probe rejected its own probe #{inspect(c.payload)} — the kernel " <>
                   "no longer returns the documented verdict for that defensive clause"
        end

        Map.new(modules, fn m -> {m, Cover.line_coverage(m)} end)
      end)

    for {mod, lines} <- @targets do
      still_cold = lines -- cov[mod].covered
      assert still_cold == [],
             "#{inspect(mod)} still cold after the kernel/probe campaign: #{inspect(still_cold)}"
    end
  end
end
