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

  describe "nodes/1 walker" do
    test "enumerates the term and all sub-terms pre-order" do
      term = {:app, {:lam, {:type, 0}, {:var, 0}}, {:int_lit, 3}}
      got = Cure.Core.Validator.nodes(term)
      assert hd(got) == term
      assert {:lam, {:type, 0}, {:var, 0}} in got
      assert {:type, 0} in got
      assert {:var, 0} in got
      assert {:int_lit, 3} in got
    end

    test "descends into case scrut/motive/branch bodies without yielding branch tuples" do
      # a branch for a constructor literally named :refl must NOT surface as a {:refl, _} node
      term = {:case, {:var, 0}, {:type, 0}, [{:refl, 1, {:var, 0}}]}
      got = Cure.Core.Validator.nodes(term)
      assert {:var, 0} in got
      assert {:type, 0} in got
      refute Enum.any?(got, &match?({:refl, _}, &1))
    end

    test "descends into data params/indices and ctor args" do
      term = {:data, :Vec, [{:int_type}], [{:int_lit, 2}]}
      got = Cure.Core.Validator.nodes(term)
      assert {:int_type} in got
      assert {:int_lit, 2} in got
    end
  end

  describe "validate/2 (Wave-0 active clauses)" do
    test "a clean current-grammar term yields no diagnostics" do
      assert {:ok, []} = Validator.validate({:lam, {:type, 0}, {:var, 0}})
    end

    test "a legacy :eq node warns under Wave-0 config" do
      assert {:ok, [w]} = Validator.validate({:eq, {:type, 0}, {:var, 0}, {:var, 0}})
      assert w.clause == :no_eq_node and w.mode == :warn
    end

    test "a hole warns under Wave-0 config (does not reject yet)" do
      assert {:ok, [w]} = Validator.validate({:hole, :h0})
      assert w.clause == :no_hole and w.mode == :warn
    end

    test "an :absurd node and a :prim node each warn" do
      assert {:ok, [%{clause: :no_absurd_node}]} = Validator.validate({:absurd})
      assert {:ok, [%{clause: :no_prim_node}]} = Validator.validate({:prim, :add, [{:int_lit, 1}, {:int_lit, 2}]})
    end

    test "config override to :reject flips admission (the per-wave flip mechanism)" do
      cfg = Map.put(Validator.wave0_config(), :no_hole, :reject)
      assert {:error, [r]} = Validator.validate({:hole, :h0}, cfg)
      assert r.clause == :no_hole and r.mode == :reject
    end
  end

  describe "deferred clauses recognize legacy shape when flipped on" do
    test "grade_on_binders fires on a current (ungraded) binder when set to :warn" do
      cfg = Map.put(Validator.wave0_config(), :grade_on_binders, :warn)
      assert {:ok, ws} = Validator.validate({:pi, {:type, 0}, {:var, 0}}, cfg)
      assert Enum.any?(ws, &(&1.clause == :grade_on_binders))
    end

    test "grade_on_binders does NOT fire on a hypothetical graded binder" do
      cfg = Map.put(Validator.wave0_config(), :grade_on_binders, :warn)
      graded = {:pi, :omega, {:type, 0}, {:var, 0}}
      assert {:ok, ws} = Validator.validate(graded, cfg)
      refute Enum.any?(ws, &(&1.clause == :grade_on_binders))
    end

    test "qualified_syms fires on a bare-atom global; level_expr fires on an integer level" do
      cfg =
        Validator.wave0_config()
        |> Map.put(:qualified_syms, :warn)
        |> Map.put(:level_expr, :warn)

      assert {:ok, ws} = Validator.validate({:app, {:global, :foo}, {:type, 2}}, cfg)
      assert Enum.any?(ws, &(&1.clause == :qualified_syms))
      assert Enum.any?(ws, &(&1.clause == :level_expr))
    end

    test "in Wave-0 config these deferred clauses stay silent (are :off)" do
      assert {:ok, []} = Validator.validate({:pi, {:type, 0}, {:global, :foo}})
    end
  end
end
