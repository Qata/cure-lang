defmodule Cure.Core.CaseSoundnessIndexTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @dec {:data, :Dec, [], []}

  # Dec with two nullary ctors; Ix(n:Dec) with wrap:(p:Dec)->Ix(Causal).
  defp base_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
         [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
    |> Inductive.declare(Inductive.family(:Ix, [], [{:n, @dec}], 0),
         [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])])
  end

  # de Bruijn (innermost = 0): in def_type Π(n).Π(h:Ix n).Π(ix:Ix n). Ix n,
  # n is var0 under its own binder, var1 under h, var2 under ix.
  @ix0 {:data, :Ix, [], [{:var, 0}]}
  @ix1 {:data, :Ix, [], [{:var, 1}]}
  @ix2 {:data, :Ix, [], [{:var, 2}]}

  # Test 1 — Positive refinement (4.3 core): reusing h : Ix n as Ix Causal.
  test "Test 1: an outer hypothesis h : Ix n is reusable as Ix Causal in the wrap branch" do
    def_type = {:pi, @dec, {:pi, @ix0, {:pi, @ix1, @ix2}}}
    motive = {:lam, @dec, {:lam, @ix0, @ix1}}
    # wrap branch adds one binder (p), so h (was var1 before the case) is var2 inside.
    body = {:lam, @dec, {:lam, @ix0, {:lam, @ix1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 2 — Refinement soundness (§5.1): the machinery does not fabricate a false
  # equation. SAME shape and SAME def_type/body as Test 1 (reusing outer hypothesis
  # `h : Ix n` in the wrap branch), but the motive now hard-demands the WRONG ground
  # index: `Ix Dcoupled` instead of `Ix Causal`. wrap's own result index is always
  # Causal, so a sound unifier can only ever derive `n := Causal` (the TRUE,
  # entailed fact) — never `n := Dcoupled`. `h`, refined to `Ix Causal`, then does
  # NOT match the required `Ix Dcoupled` (both rigid ground terms of the SAME
  # family Ix, per design §8 item 2), so the case must still be rejected. This is
  # the direction Test 1 does not cover: Test 1 shows a previously-rejected good
  # program now accepts; this shows the same machinery does not go on to fabricate
  # an equation the match never actually established.
  test "Test 2: a body relying on an unentailed index equation is still rejected" do
    def_type = {:pi, @dec, {:pi, @ix0, {:pi, @ix1, {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}}}}
    motive = {:lam, @dec, {:lam, @ix0, {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}}}
    body = {:lam, @dec, {:lam, @ix0, {:lam, @ix1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, _} = Kernel.check_def(env, :probe)
  end

  # Test 4 — Occurs-check (§5.3), regression half. Given the proven disjoint-range
  # invariant (§4.4: r-side vars always < arity, s-side vars always >= arity after
  # reify+shift), a real cyclic pair cannot arise from any legitimate case branch —
  # so no adversarial construction exists to positively exercise occurs_index?/2
  # returning true on real input while keeping this test green pre-fix (any
  # fixture that meaningfully drives the new var-var solving path is, by
  # construction, a NEW-capability case like Test 1/2, not a same-behavior
  # regression). This test instead documents the honest, weaker claim: a
  # legitimate bare-ctor-arg-var match (the one case today's kernel already
  # handles) keeps checking unchanged under the new unifier — i.e. the occurs-check
  # machinery, even though present on every bind, adds no false rejections on
  # ordinary structural-recursion input. It does NOT prove the guard would
  # actually catch a genuine cycle (no such input is constructible here); that
  # guarantee rests on the disjoint-range proof in §4.4, not on this test.
  test "Test 4: structural-recursion refinement of a nested-index family still checks" do
    # Two(i:Dec) with pack:(y:Dec)->Two(y); match Two(m) with variable m → bind m := y.
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
      |> Inductive.declare(Inductive.family(:Two, [], [{:i, @dec}], 0),
           [Inductive.ctor(:pack, [{:y, @dec}], [{:var, 0}])])
    two0 = {:data, :Two, [], [{:var, 0}]}
    def_type = {:pi, @dec, {:pi, two0, @dec}}          # Π(m:Dec). Π(t:Two m). Dec
    motive = {:lam, @dec, {:lam, two0, @dec}}          # λm'.λt'. Dec
    body = {:lam, @dec, {:lam, two0, {:case, {:var, 0}, motive, [{:pack, 1, {:var, 0}}]}}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 5b — Undecidable half (§5.4, monotonic degradation): a pairing the
  # unifier cannot classify as either a solvable variable or a rigid clash must
  # stay :undecided (never :impossible) and the branch must NOT be discharged.
  # A "good body, assert :ok" framing CANNOT prove this: a wrongly-discharged
  # branch and a correctly-checked-and-accepted branch are both observably :ok,
  # so no such test can distinguish them. Instead: a fresh family `Stray(n:Dec)`
  # whose only constructor's result index is one opaque global (`h`); the
  # scrutinee's own index is a DIFFERENT opaque global (`g`). Neither side is a
  # de Bruijn variable (so unify_one's var-solving clauses never fire) and
  # neither is `rigid_index?/1` (a bare `{:global, _}` is not in that predicate's
  # clauses), so the pair is genuinely :undecided in BOTH Task 1 and Task 2 —
  # it can never become :impossible. The branch is given a deliberately
  # ill-typed body (`{:type, 0}`); a kernel that wrongly discharged this branch,
  # or wrongly fabricated a binding from it, would return :ok. The correct,
  # conservative kernel does not discharge it, checks the body against the
  # constant motive's `Dec` requirement, and rejects it.
  test "Test 5b: an undecidable index does not skip the body check" do
    env =
      base_env()
      |> Inductive.declare(Inductive.family(:Stray, [], [{:n, @dec}], 0),
           [Inductive.ctor(:mkStray, [{:p, @dec}], [{:global, :h}])])
      |> Env.add_def(:g, @dec, {:ctor, :Causal, []})
    stray_g = {:data, :Stray, [], [{:global, :g}]}
    motive = {:lam, @dec, {:lam, {:data, :Stray, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, stray_g, @dec}                    # Π(s: Stray(global g)). Dec
    body = {:lam, stray_g, {:case, {:var, 0}, motive, [{:mkStray, 1, {:type, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert {:error, :branch_type} = Kernel.check_def(env, :probe)
  end

  # Test 7 — Regression: the legit Box/Dec matches (mirrors case_typing_test) still
  # check; here we just re-assert a ground-indexed match refines the ctor arg.
  test "Test 7: ground-indexed Box match still refines the ctor argument (no regression)" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
      |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0),
           [Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])])
    box_causal = {:data, :Box, [], [{:ctor, :Causal, []}]}
    motive = {:lam, @dec, {:lam, {:data, :Box, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, box_causal, @dec}                 # Π(b:Box Causal). Dec
    body = {:lam, box_causal, {:case, {:var, 0}, motive, [{:mk, 1, {:var, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end
end
