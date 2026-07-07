defmodule Cure.Core.ValidatorTest do
  # async: false — Task 5 adds a test that calls `Application.put_env(:cure,
  # :final_core_config, …)`. That key is process-independent GLOBAL state read
  # by `Kernel.check_def/2` (the shared TCB entry point every other `test/cure/core/`
  # suite also calls). Running this file concurrently with another async suite
  # while the override is live would risk a spurious cross-file rejection the
  # moment any other suite's checked def contains a hole. Given this codebase's
  # own history of kernel-related test-concurrency hazards (see Global
  # Constraints), keep this whole file serial rather than relying on no other
  # suite ever adding a hole-bearing `check_def` call.
  use ExUnit.Case, async: false
  alias Cure.Core.Validator

  describe "clause registry and Wave-0 config" do
    test "wave0_config assigns a mode to every registered clause and no others" do
      assert MapSet.new(Map.keys(Validator.wave0_config())) == MapSet.new(Validator.clauses())
    end

    test "no clause is :reject in Wave 0 (pure instrumentation)" do
      refute Enum.any?(Validator.wave0_config(), fn {_c, mode} -> mode == :reject end)
    end

    test "legacy-detecting clauses warn; not-yet-reshaped clauses are off" do
      cfg = Validator.wave0_config()
      assert cfg.no_hole == :warn
      assert cfg.no_eq_node == :warn
      assert cfg.no_prim_node == :warn
      assert cfg.no_absurd_node == :warn
      assert cfg.grade_on_binders == :off
      assert cfg.qualified_syms == :off
      assert cfg.level_expr == :off
    end
  end
end
