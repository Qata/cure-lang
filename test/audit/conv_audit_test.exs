defmodule Cure.Audit.ConvTest do
  @moduledoc """
  Audit findings for `lib/cure/core/conv.ex` (the trusted definitional-equality
  / conversion checker).

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test
  for the bug, why it is wrong, and what the reference implementations
  (Agda/Lean/Idris) do instead. Do not run this file automatically as part
  of the trusted-suite gate — it documents open findings, not yet-fixed
  regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.{Conv, Normalise}

  # C1: `Conv.conv_within?/6` (conv.ex ~40-44) is the ONLY public entry point
  # that bounds conversion's δ-unfold count — it is the "reflexivity assay's
  # oracle" that Antigen relies on to catch a certified-but-actually-diverging
  # global (a totality-certifier soundness hole) instead of hanging. It works
  # by delegating straight to `Normalise.with_fuel/2`, which tracks the
  # remaining budget in the PROCESS DICTIONARY under one fixed key
  # (`Normalise.fuel_key/0`):
  #
  #     def with_fuel(fuel, fun) when is_integer(fuel) and fuel > 0 do
  #       Process.put(@fuel_key, fuel)
  #       try do
  #         fun.()
  #       catch
  #         :throw, {@fuel_key, :exhausted} -> :fuel_exhausted
  #       after
  #         Process.delete(@fuel_key)
  #       end
  #     end
  #
  # The `after` clause unconditionally *deletes* the key on the way out — it
  # never saves the PREVIOUS value and restores it. Nothing in `conv_within?`
  # or `with_fuel` forbids calling `conv_within?` again while already inside
  # an outer fueled scope (nothing stops, say, one Antigen assay helper
  # reusing another that also calls `conv_within?`, or a future caller
  # composing two fuel-bounded checks). When that happens, the inner call's
  # cleanup wipes the OUTER scope's fuel key entirely. Any further δ-spending
  # in the outer computation then hits `spend_fuel`'s `nil -> reduced` clause
  # (normalise.ex), which treats a *missing* key as "unlimited" rather than
  # "exhausted" — silently disabling the very bound the outer caller asked
  # for, instead of failing loudly or correctly resuming with the remaining
  # budget. This is exactly the "fuel in the process dictionary, not
  # nest-safe" hazard the kernel audit already flagged and left unresolved
  # (`docs/superpowers/raw_audit.txt` #530/#583/#409: "Nested normalization
  # can clobber outer fuel unless restored carefully... This is not
  # reproducible checker state"; `docs/superpowers/audit_categorised.md`'s K8
  # section — unlike every other K-category — has no assessment/resolution
  # paragraph).
  #
  # Lean, Agda, and Idris keep checker state (including step/fuel counters
  # where they exist) explicit in a context or monad specifically so nested
  # sub-computations compose without clobbering an enclosing computation's
  # state. A sound fuel discipline here must let an independent nested fueled
  # conversion run to completion without disturbing an enclosing scope's
  # remaining budget: the outer counter should read unchanged once the inner
  # call returns.
  test "C1: a nested conv_within? call must not wipe the enclosing fuel budget" do
    outer_fuel = 5

    fuel_after_inner_call =
      Normalise.with_fuel(outer_fuel, fn ->
        # An unrelated, independent fueled conversion, nested inside the
        # outer fueled scope (e.g. a helper shared by two composed
        # assays/oracles). It trivially succeeds and, since `sig` is `nil`,
        # never even attempts a δ-unfold of its own.
        assert {:ok, true} = Conv.conv_within?({:type, 0}, {:type, 0}, [], 0, nil, 1)

        # The outer scope's own fuel counter should still be intact here —
        # the inner call was a self-contained, independently-fueled
        # computation and should not have touched it.
        Process.get(Normalise.fuel_key())
      end)

    assert fuel_after_inner_call == outer_fuel,
           "the inner conv_within? call's cleanup wiped the enclosing fuel counter " <>
             "(got #{inspect(fuel_after_inner_call)}, expected #{outer_fuel} unchanged) — " <>
             "conv_within?/Normalise.with_fuel's process-dictionary fuel state is not " <>
             "nest-safe, silently disabling the outer caller's fuel bound"
  end
end
