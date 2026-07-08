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

  describe "check_def_config/0 and kernel wiring" do
    alias Cure.Core.{Validator, Env, Kernel}

    test "check_def_config defaults to the Wave-0 config" do
      assert Validator.check_def_config() == Validator.wave0_config()
    end

    test "a clean def still admits under the default (non-breaking)" do
      # idty : Type 0 -> Type 0  ;  body = λx. x  (clean, admits)
      env = Env.add_def(Env.empty(), :idty, {:pi, {:type, 0}, {:type, 0}}, {:lam, {:type, 0}, {:var, 0}})
      assert :ok == Kernel.check_def(env, :idty)
    end

    test "with a reject-override config, a hole-bearing def fails admission" do
      env = Env.add_def(Env.empty(), :withhole, {:pi, {:type, 0}, {:type, 0}}, {:lam, {:type, 0}, {:hole, :h}})

      Application.put_env(:cure, :final_core_config, Map.put(Validator.wave0_config(), :no_hole, :reject))
      on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

      assert {:error, {:final_core_violation, [%{clause: :no_hole}]}} = Kernel.check_def(env, :withhole)
    end

    test "a legacy node in the declared TYPE is caught too, not just the body" do
      # helper : Eq(Int, 1, 1) ; body = refl(1) — a legacy `:eq` node used AS a
      # definition's type (still typeable pre-K1). `eqty` reuses that same `:eq`
      # type but its body is a clean `{:global, :helper}` reference, so the ONLY
      # legacy node reachable from `eqty`'s own {type_term, body_term} pair is in
      # its type_term. If the wiring only scanned body_term (the pre-fix shape),
      # this def would wrongly admit even under a :reject override.
      eq_ty = {:eq, {:int_type}, {:int_lit, 1}, {:int_lit, 1}}

      env =
        Env.empty()
        |> Env.add_def(:helper, eq_ty, {:refl, {:int_lit, 1}})
        |> Env.add_def(:eqty, eq_ty, {:global, :helper})

      Application.put_env(:cure, :final_core_config, Map.put(Validator.wave0_config(), :no_eq_node, :reject))
      on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

      assert {:error, {:final_core_violation, rejections}} = Kernel.check_def(env, :eqty)
      assert Enum.any?(rejections, &(&1.clause == :no_eq_node))
    end

    test "a violating node in the declared TYPE is caught too — post-retirement probe" do
      # Phase C twin of the legacy-node test above (added FIRST, per the
      # add-then-retire protocol): once the primitive `{:eq}`/`{:refl}` kernel
      # clauses are removed, that fixture can no longer REACH the validator —
      # `check_def` kernel-typechecks type and body BEFORE the final-Core scan,
      # and a primitive node is then unknown grammar there. The wiring property
      # it proved (the scan covers the declared TYPE, not just the body) is
      # re-proved here with current-grammar nodes: `natalias`'s TYPE is a
      # bare-atom `{:global, …}` reference (a `qualified_syms` violation), its
      # body a hole (kernel-accepted at any goal; only a `no_hole` WARN under
      # this config). Under a `qualified_syms: :reject` override the rejection
      # can therefore only originate in the type_term scan.
      {:ok, env0} = Cure.Elab.Program.elaborate("mod M\nend\n")

      env =
        env0
        |> Env.add_def(:natty, {:type, 0}, {:data, :Nat, [], []})
        |> Env.add_def(:natalias, {:global, :natty}, {:hole, "inhabit"})

      cfg = Map.put(Validator.wave0_config(), :qualified_syms, :reject)
      Application.put_env(:cure, :final_core_config, cfg)
      on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

      assert {:error, {:final_core_violation, rejections}} = Kernel.check_def(env, :natalias)
      assert Enum.any?(rejections, &(&1.clause == :qualified_syms))
    end
  end

  describe "release_config/0 (the strict ratchet, K3)" do
    test "no_hole is :reject in release mode" do
      assert Validator.release_config()[:no_hole] == :reject
    end

    test "no_absurd_node is :reject in release mode (K4 — the node is gone from final Core)" do
      assert Validator.release_config()[:no_absurd_node] == :reject
      assert {:error, rejections} = Validator.validate({:absurd}, Validator.release_config())
      assert Enum.any?(rejections, &(&1.clause == :no_absurd_node))
    end

    test "every registered clause has a mode in release_config, and none is looser than Wave-0" do
      rel = Validator.release_config()
      assert MapSet.new(Map.keys(rel)) == MapSet.new(Validator.clauses())
      # release only tightens: a clause never becomes :off/:warn where Wave-0 was stricter
      rank = %{off: 0, warn: 1, reject: 2}
      w0 = Validator.wave0_config()
      for c <- Validator.clauses(), do: assert(rank[rel[c]] >= rank[w0[c]], "clause #{c} loosened")
    end

    test "rejects a hole hidden in an erased (rewrite-proof) position — the #102 leak" do
      # Erase would drop the rewrite proof, but the validator descends into it.
      term = {:rewrite, {:hole, "p"}, {:type, 0}, {:ctor, :ok, []}}
      assert {:error, rejections} = Validator.validate(term, Validator.release_config())
      assert Enum.any?(rejections, &(&1.clause == :no_hole))
    end

    test "still admits a hole-free, node-clean term" do
      assert {:ok, _warnings} = Validator.validate({:ctor, :ok, []}, Validator.release_config())
    end

    test "no_eq_node is :reject in release (K1a — primitive eq/refl retired from produced Core)" do
      assert Validator.release_config()[:no_eq_node] == :reject
      # primitive refl: dead-producer (bridge_step migrated to inductive refl,
      # f3b0e73; surface refl + symmetry_proof already inductive) → rejected.
      assert {:error, rj_refl} = Validator.validate({:refl, {:int_lit, 1}}, Validator.release_config())
      assert Enum.any?(rj_refl, &(&1.clause == :no_eq_node))
      # primitive :eq type-former: no producers (mk_eq builds inductive {:data,:Eq}) → rejected.
      eq = {:eq, {:int_type}, {:int_lit, 1}, {:int_lit, 1}}
      assert {:error, rj_eq} = Validator.validate(eq, Validator.release_config())
      assert Enum.any?(rj_eq, &(&1.clause == :no_eq_node))
    end

    test "primitive :rewrite only WARNS in release (Phase B pending — still the transport eliminator)" do
      # Retiring {:rewrite} (rewrite→single-branch :case) is Phase B, a structural
      # re-plumbing (the body scopes differently: outer-context for {:rewrite} vs
      # under the refl branch binder for :case). Until it lands, {:rewrite} must
      # NOT block release, else every rewrite-using program's final Core is rejected.
      rw = {:rewrite, {:ctor, :refl, [{:int_type}, {:int_lit, 1}]}, {:type, 0}, {:ctor, :ok, []}}
      assert {:ok, ws} = Validator.validate(rw, Validator.release_config())
      assert Enum.any?(ws, &(&1.clause == :no_rewrite_node and &1.mode == :warn))
    end
  end
end
