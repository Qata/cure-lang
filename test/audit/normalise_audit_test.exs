defmodule Cure.Audit.NormaliseTest do
  @moduledoc """
  Audit findings for `lib/cure/core/normalise.ex` (TCB: the δ/ι-fuel-gated
  normalizer). See the accompanying audit report for the full write-up; this
  file only carries the executable claims.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.{Context, Env, Normalise}

  # --------------------------------------------------------------------------
  # Finding 1: `with_fuel/2` is a process-dictionary dynamic-scope counter that
  # does NOT save/restore across reentrant (nested) calls. Its `after` clause
  # unconditionally `Process.delete`s the shared key, so when a
  # `Normalise.with_fuel`-wrapped call (including any `Normalise.nf/3` or
  # `Normalise.whnf/3` call, both of which route through `run_with_fuel/2` ->
  # `with_fuel/2`) runs to completion *while already nested inside another
  # `with_fuel` scope*, it silently wipes the OUTER scope's remaining budget
  # to "untracked" instead of restoring it. `spend_fuel/1` treats an absent
  # key as "unlimited" (`nil -> reduced`, no decrement, never throws), so the
  # outer computation's requested fuel bound becomes unenforceable for the
  # rest of its lifetime — exactly the "fuel exhaustion silently returning a
  # term as if fully normal" hazard: the caller asked for a bounded, replayable
  # step count (this is literally `Conv.conv_within?`'s stated contract: "a
  # suspected non-normalization... a fixed step count, so it is
  # machine-independent and replayable") and gets an unbounded one instead,
  # with no signal that the bound was dropped.
  #
  # The correct fix is standard dynamic-scope save/restore: `with_fuel/2` must
  # remember whatever value (or absence) occupied the fuel key BEFORE it ran,
  # and put that back in its `after` clause, rather than unconditionally
  # deleting. This is the same discipline Idris/Lean use for nested elaboration
  # "budget" parameters — never module a shared mutable counter without
  # save/restore across reentry.
  # --------------------------------------------------------------------------

  describe "N1: with_fuel reentrancy corrupts the ambient fuel budget" do
    test "N1: a nested with_fuel call wipes an outer, still-live fuel counter instead of restoring it" do
      key = Normalise.fuel_key()

      # Simulate being partway through an OUTER `with_fuel` scope that still
      # has 7 units of budget remaining (as any caller composing two fueled
      # calls would be, the moment the first call's `fun` invokes the second).
      Process.put(key, 7)

      # A fully independent, nested/reentrant fueled call — this is exactly
      # what `Normalise.nf/3` or `Normalise.whnf/3` do internally
      # (`run_with_fuel` -> `with_fuel`), so any caller invoking either from
      # inside another fueled computation hits this path.
      assert :inner_done == Normalise.with_fuel(3, fn -> :inner_done end)

      # A correctly save/restore-scoped implementation leaves the OUTER
      # counter exactly as it found it once the nested call returns — nesting
      # a bounded sub-computation must not affect budget accounting outside
      # its own scope. Instead, `with_fuel`'s `after` clause unconditionally
      # `Process.delete`s the shared key, so the outer counter is gone.
      assert Process.get(key) == 7,
             "outer fuel counter was #{inspect(Process.get(key))} after a nested with_fuel " <>
               "call returned; expected the pre-nesting value (7) to be restored"
    after
      Process.delete(Normalise.fuel_key())
    end
  end

  describe "N2: the same corruption breaks a real Normalise.nf/whnf-driven fuel budget" do
    defp one_step_env do
      Env.empty()
      |> Env.add_def(:one_step, {:int_type}, {:int_lit, 99})
      |> Env.certify(:one_step)
    end

    test "N2: a reentrant Normalise.whnf/3 call inside a fueled computation lets the outer budget run unbounded" do
      env = one_step_env()
      ctx = Context.empty(env)

      # `:one_step` is a certified global whose body is a closed literal, so
      # δ-unfolding it costs exactly ONE `spend_fuel` call (mirrors the
      # existing "fuel exhaustion is deterministic for cyclic certified delta"
      # sibling test in test/cure/core/normalise_test.exs, which establishes
      # the same one-step-per-unfold accounting).
      result =
        Normalise.with_fuel(2, fn ->
          # Reentrant/nested fueled call, its OWN independent 1-unit budget.
          # This is exactly what any composition of Normalise.nf/whnf calls
          # triggers (e.g. a future caller that normalizes a sub-term via
          # Normalise.whnf/3 from inside a callback passed to another
          # Normalise.nf/3 or Normalise.with_fuel call).
          assert {:int_lit, 99} == Normalise.whnf(ctx, {:global, :one_step}, fuel: 1)

          # Back in the OUTER scope: the outer counter was never spent before
          # the nested call, so a correctly-scoped implementation still has
          # its full 2-unit budget here. Spend 3 MORE certified unfolds
          # directly against it (same `:one_step` global, each one legitimate
          # δ-progress, exactly the kind of work `nf`/`whnf` do while walking
          # a real term) — with 2 units actually remaining, the 3rd of these
          # must exhaust and throw before completing.
          for _ <- 1..3 do
            Normalise.whnf_value({:vneutral, {:nglobal, :one_step}}, env, delta: :certified)
          end

          :outer_survived_without_exhaustion
        end)

      assert result == :fuel_exhausted,
             "outer fuel budget (2 units) survived 3 more certified unfolds unexhausted " <>
               "after a reentrant Normalise.whnf/3 call — got #{inspect(result)} instead of " <>
               ":fuel_exhausted; the nested call wiped fuel tracking instead of restoring it"
    end
  end
end
