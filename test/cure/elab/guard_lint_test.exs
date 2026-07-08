defmodule Cure.Elab.GuardLintTest do
  @moduledoc """
  Spec 2026-07-08-guard-coverage-lint: the untrusted Z3 coverage lint. Unit
  describe drives GuardLint directly on hand-built Core; the integration
  describe (Task 2) drives it through Program.elaborate/1.
  """
  use ExUnit.Case, async: false

  alias Cure.Core.Context
  alias Cure.Elab.GuardLint

  # Context with two machine-Int vars: index 0 and index 1.
  defp int_ctx do
    Context.empty() |> Context.extend({:vint_type}) |> Context.extend({:vint_type})
  end

  defp p(op, a, b), do: {:prim, op, [a, b]}
  @x {:var, 0}
  @y {:var, 1}

  describe "prove_exhaustive/2 (§2.2 fragment, §2.3a recovery oracle)" do
    test "trichotomy over Int is proven" do
      assert :proven =
               GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:eq, @x, @y), p(:gt, @x, @y)], int_ctx())
    end

    test "a complement pair is proven" do
      assert :proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:ge, @x, @y)], int_ctx())
    end

    test "an Int-only cover is proven over Int (documents the fragment's Int semantics)" do
      # x <= 0 | x >= 1 — exhaustive over Int, NOT over Float; translatable only
      # because the vars are Int-typed in ctx (a Float var falls out at int_form).
      assert :proven =
               GuardLint.prove_exhaustive(
                 [p(:le, @x, {:int_lit, 0}), p(:ge, @x, {:int_lit, 1})],
                 int_ctx()
               )
    end

    test "a genuine gap is not proven" do
      assert :not_proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), p(:gt, @x, @y)], int_ctx())
    end

    test "a Float-typed variable makes its guard untranslatable (not proven)" do
      ctx = Context.empty() |> Context.extend({:vfloat_type}) |> Context.extend({:vfloat_type})
      assert :not_proven = GuardLint.prove_exhaustive([p(:le, @x, {:int_lit, 0}), p(:ge, @x, {:int_lit, 1})], ctx)
    end

    test "an untranslatable guard can never help prove exhaustiveness (K13)" do
      mystery = {:ctor, :Mystery, [@x]}
      assert :not_proven = GuardLint.prove_exhaustive([mystery], int_ctx())
      assert :not_proven = GuardLint.prove_exhaustive([p(:lt, @x, @y), mystery], int_ctx())
    end

    test "the empty guard list is not proven" do
      assert :not_proven = GuardLint.prove_exhaustive([], int_ctx())
    end
  end

  describe "shadowed?/3" do
    test "a literally repeated translatable guard is shadowed" do
      assert GuardLint.shadowed?(p(:lt, @x, @y), [p(:lt, @x, @y)], int_ctx())
    end

    test "an implied guard is shadowed" do
      # x < y implies x <= y
      assert GuardLint.shadowed?(p(:lt, @x, @y), [p(:le, @x, @y)], int_ctx())
    end

    test "a non-implied guard is not shadowed" do
      refute GuardLint.shadowed?(p(:gt, @x, @y), [p(:lt, @x, @y)], int_ctx())
    end

    test "no priors -> never shadowed" do
      refute GuardLint.shadowed?(p(:lt, @x, @y), [], int_ctx())
    end

    test "a literally repeated UNtranslatable guard is shadowed via atom interning (§2.2)" do
      g = {:ctor, :Mystery, [@x]}
      assert GuardLint.shadowed?(g, [g], int_ctx())
    end

    test "distinct untranslatable guards are not shadowed (distinct constants)" do
      refute GuardLint.shadowed?({:ctor, :MysteryB, [@x]}, [{:ctor, :MysteryA, [@x]}], int_ctx())
    end
  end

  describe "warnings channel (§2.5)" do
    test "record/read/reset round-trip in insertion order" do
      GuardLint.reset_warnings()
      assert GuardLint.warnings() == []
      GuardLint.record_warning({:guard_shadowed, 1})
      GuardLint.record_warning({:guard_shadowed, 2})
      assert GuardLint.warnings() == [{:guard_shadowed, 1}, {:guard_shadowed, 2}]
      GuardLint.reset_warnings()
      assert GuardLint.warnings() == []
    end
  end
end
