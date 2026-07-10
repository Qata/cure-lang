defmodule Cure.Audit.GuardLintTest do
  @moduledoc """
  Audit findings for lib/cure/elab/guard_lint.ex (the untrusted Z3
  guard-coverage lint, spec 2026-07-08-guard-coverage-lint).

  Scope note: the recognizer (`bool_form`/`int_form`), the K13
  untranslatable-never-proves rule, the exhaustiveness/shadow SMT encodings,
  and the trap_exit-hardened Z3 process isolation were all read tip-to-tail
  and cross-checked against `lib/cure/core/builtins.ex` (the current
  delta-global registry) and `lib/cure/core/term.ex` (the current Core node
  grammar). All of that held up: the prim recognizer already targets the
  live `{:app, {:app, {:global, g}, a}, b}` builtin-op spine via
  `Env.builtin_op/2` (not a stale `{:prim, op, args}` shape), Nat/Bounded
  variables are excluded from the Int fragment by the `{:vint_type}` gate
  (so no Nat-as-Int negative-value unsoundness), and every Z3 failure mode
  (`:sat`/`:unknown`/timeout/crash/absence) degrades to the conservative
  outcome on both `prove_exhaustive/2` and `shadowed?/3`. See the final
  report for the one architectural point (Z3-proof gating the final guarded
  arm's acceptance at `elaborator.ex`'s `guard_chain/7`) that was
  deliberately re-derived and found to match the locked, already-documented
  soundness argument in the spec (§2.3a) — not a new finding, so no test is
  filed for it.

  This file holds the one genuine, testable finding.
  """

  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{GuardLint, Program}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  # G1: shadow-warning order is REVERSED (descending arm index) once a chain
  # has 2+ shadowed guarded arms, contradicting GuardLint's own documented
  # contract and the plain meaning of "insertion order" pinned by
  # `test/cure/elab/guard_lint_test.exs`'s
  # "record/read/reset round-trip in insertion order" test.
  #
  # Root cause (cross-file, surfaces through GuardLint's public warnings
  # channel): `lib/cure/elab/elaborator.ex`'s `guard_chain/7` multi-arm
  # clause (~2812-2830) calls
  #
  #     {:ok, ff} <- guard_chain(scrut_expr, rest, expected, names, ctx, env, acc ++ [test])
  #     maybe_warn_shadowed(test, acc, ctx)
  #
  # i.e. it recurses into every LATER arm (which runs THEIR OWN
  # `maybe_warn_shadowed` calls, and therefore `GuardLint.record_warning/1`
  # calls) BEFORE checking/recording the CURRENT (earlier) arm's own shadow
  # status. So for a chain with guarded arms at source indices 1 and 2 both
  # shadowed, `GuardLint.record_warning/1` is called for index 2 FIRST
  # (chronologically) and index 1 SECOND. `GuardLint.record_warning/1`
  # prepends and `GuardLint.warnings/0` reverses that prepended list — a
  # mechanism that correctly restores insertion order when the CALLER
  # inserts in source order (as the unit-level round-trip test verifies in
  # isolation) but here the caller itself inserts out of order, so the
  # reversal produces `[index2, index1]` instead of `[index1, index2]`.
  #
  # Impact: today this is diagnostics-only (no CLI/stderr consumer yet per
  # spec §7), so it is not a soundness hole — but it is a concrete
  # correctness bug in the one channel this file exposes for shadow
  # warnings, and it will silently corrupt any future consumer's ordering
  # (e.g. "which duplicate guard fired first" in an editor/CLI diagnostic).
  #
  # This test needs a real Z3 binary on PATH to observe the CORRECT
  # behavior (shadow detection requires an :unsat verdict). If Z3 is
  # absent, `shadowed?/3` degrades to `false` for every guard (conservative
  # per §2.3), so `GuardLint.warnings()` comes back `[]` — which still
  # fails this assertion loudly (never silently skips), satisfying the
  # audit's "fail loudly, don't skip silently" requirement either way.
  test "G1: shadow warnings for 2+ shadowed arms come back in source order, not reversed" do
    src =
      @nat <>
        "  fn cls(n: Int, b: Int) -> Nat = match n\n" <>
        "    x when x < b -> Z()\n" <>
        "    x when x < b -> S(Z())\n" <>
        "    x when x < b -> S(S(Z()))\n" <>
        "    x -> S(S(S(Z())))\nend\n"

    assert {:ok, _env} = Program.elaborate(src)

    # Arm 1 (2nd guarded arm, 0-based) is shadowed by arm 0; arm 2 (3rd
    # guarded arm) is shadowed by arm 0 \/ arm 1. Both fire. The correct,
    # documented "insertion order" (matching the source top-to-bottom
    # order the arms were elaborated in) is ascending: index 1 before
    # index 2. The actual bug returns them descending: [2, 1].
    assert GuardLint.warnings() == [{:guard_shadowed, 1}, {:guard_shadowed, 2}]
  end
end
