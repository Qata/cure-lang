defmodule Antigen.Assays.ErasureTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Erasure, Challenge}
  alias Antigen.Generators.ErasureTerm
  alias Cure.Core.{Env, Inductive}

  defp il(n), do: {:int_lit, n}
  defp ctor_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:P, [], [], 0), [
         Inductive.ctor(:MkQ, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:present, :erased]),
         Inductive.ctor(:MkP, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:erased, :present])
       ])
  end

  defp idem_ch(env, t) do
    Challenge.new(kind: :erasure_term, assay: "erasure/idempotent", label: :positive,
      payload: %{env: env, term: t}, seed: 1)
  end

  # app-head defs: f present-first (clean), g erased-first (the finding). Defined
  # once here at module level (NOT re-declared by Task 2's describe block) so both
  # this task's app-head known-finding test and Task 2's selective tests share it.
  defp app_env(env) do
    ty = {:pi, {:int_type}, {:pi, {:int_type}, {:int_type}}}
    env
    |> Env.add_def(:f, ty, {:int_lit, 0}, [:present, :erased])
    |> Env.add_def(:g, ty, {:int_lit, 0}, [:erased, :present])
  end
  defp app2(head, x0, x1), do: {:app, {:app, head, x0}, x1}

  test "idempotent baseline: present-first ctor erases idempotently" do
    env = ctor_env()
    assert Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
  end

  test "hole-preservation baseline: a hole-free term stays hole-free after erase" do
    env = ctor_env()
    assert Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
  end

  test "idempotent negative control: a wrapping erase stub is not a fixpoint" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, t -> {:ctor, :Wrap, [t]} end}
    assert {:violation, {:erase_not_idempotent, _}} = Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
  end

  test "hole negative control: an erase stub that introduces a hole is caught" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, _t -> {:hole, :x} end}
    assert {:violation, {:hole_introduced, _}} = Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
  end

  describe "known erase/2 non-idempotence finding (spec §3, §9-2/§9-3)" do
    # These terms are NOT in erase_challenges/0 (reconciliation #1). The assay is
    # CORRECT — it reports the real erase's non-idempotence as a violation. This
    # documents a genuine, spec-review-traced, currently-dormant erase/2 defect.
    test "ctor erased-before-present ordering: real erase is non-idempotent (TRUE POSITIVE)" do
      env = ctor_env()
      assert {:violation, {:erase_not_idempotent, _}} = Erasure.run(idem_ch(env, {:ctor, :MkP, [il(1), il(2)]}))
    end

    # Second surface (spec §3/§9-item-3): the app-head clause has the identical
    # zip-realignment hazard as the :ctor clause. `g`'s quantities are
    # [:erased, :present]; once = erase(env, app2(g,1,2)) = {:app,{:global,g},il(2)}
    # (arg 0 dropped, arg 1 kept); twice re-erases from a 1-arg spine against the
    # SAME full 2-element quantity vector, re-zipping the survivor to qs[0] =
    # :erased and dropping it -> {:global, g} (bare head, no args). This is the
    # app-head counterpart to the ctor finding above — NOT a member of
    # erase_challenges/0 (Task 5), for the same reason.
    test "app-head erased-before-present ordering: real erase is non-idempotent (TRUE POSITIVE)" do
      env = app_env(ctor_env())
      assert {:violation, {:erase_not_idempotent, _}} =
               Erasure.run(idem_ch(env, app2({:global, :g}, il(1), il(2))))
    end
  end

  describe "erasure/selective (V4a)" do
    defp sel_ch(env, t, surface) do
      Challenge.new(kind: :erasure_term, assay: "erasure/selective", label: :positive,
        payload: %{env: env, term: t, surface: surface}, seed: 1)
    end

    test "ctor selective baseline: keeps exactly the :present positions (leaf args)" do
      env = ctor_env()
      assert Erasure.run(sel_ch(env, {:ctor, :MkQ, [il(1), il(2)]}, :ctor)) == :ok
    end

    test "app-head selective baseline: keeps exactly the :present def positions (leaf args)" do
      env = app_env(ctor_env())
      assert Erasure.run(sel_ch(env, app2({:global, :f}, il(1), il(2)), :app)) == :ok
    end

    test "ctor selective negative control: an erase stub dropping the :present position" do
      env = ctor_env()
      k = %{Erasure.__real__() | erase: fn _e, {:ctor, c, _args} -> {:ctor, c, []} end}
      assert {:violation, {:wrong_positions_kept, :MkQ}} = Erasure.run(sel_ch(env, {:ctor, :MkQ, [il(1), il(2)]}, :ctor), k)
    end

    test "app-head selective negative control: an erase stub dropping a :present arg" do
      env = app_env(ctor_env())
      k = %{Erasure.__real__() | erase: fn _e, _t -> {:global, :f} end}  # drops all args
      assert {:violation, {:wrong_positions_kept, :f}} = Erasure.run(sel_ch(env, app2({:global, :f}, il(1), il(2)), :app), k)
    end
  end
end
