defmodule Cure.Core.BoolElimTest do
  @moduledoc """
  The dependent Boolean eliminator `{:bool_elim, scrut, motive, tt, ff}` — Lean's
  `Bool.rec`. This is the minimal sound primitive eliminator: `{:prim}` already
  types `==`/`<`/`&&` at `Bool` and reduces them to `{:vbool, _}`, so branching on
  a `Bool` is the only kernel primitive missing to unlock guards, `if`, and
  integer/atom/float literal patterns (all of which desugar in the *untrusted*
  elaborator to `prim` comparisons feeding this eliminator).

  Total by construction: exactly two branches, both mandatory — no coverage rule,
  no default, no literal-matching in the kernel.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Eval, Conv, Certificate, Term, Value, Env}

  # λ_:Bool. Int — the non-dependent (constant) motive used by guards/literals.
  @const_motive {:lam, {:bool_type}, {:int_type}}

  describe "term.ex structure" do
    test "a well-formed bool_elim is a term" do
      t = {:bool_elim, {:bool_lit, true}, @const_motive, {:int_lit, 1}, {:int_lit, 0}}
      assert Term.term?(t)
    end

    test "shift/subst descend into all four sub-terms at the same depth" do
      t = {:bool_elim, {:var, 0}, @const_motive, {:var, 0}, {:var, 1}}
      assert {:bool_elim, {:var, 2}, @const_motive, {:var, 2}, {:var, 3}} = Term.shift(t, 2, 0)
      # substitute var 0 := 5 (bool_elim binds nothing, so index is unshifted)
      assert {:bool_elim, {:int_lit, 5}, @const_motive, {:int_lit, 5}, {:var, 1}} =
               Term.subst(t, 0, {:int_lit, 5})
    end

    test "serialization round-trips" do
      t = {:bool_elim, {:bool_lit, false}, @const_motive, {:int_lit, 1}, {:int_lit, 0}}
      assert ^t = t |> Term.to_external() |> Term.from_external()
    end

    test "the stuck neutral is a well-formed value" do
      {:vneutral, n} =
        Eval.eval({:bool_elim, {:var, 0}, @const_motive, {:int_lit, 1}, {:int_lit, 0}}, [
          {:vneutral, {:nvar, 0}}
        ])

      assert Value.neutral?(n)
    end
  end

  describe "eval ι-reduction" do
    test "reduces to the true-branch on true" do
      assert {:vint, 7} ==
               Eval.eval({:bool_elim, {:bool_lit, true}, @const_motive, {:int_lit, 7}, {:int_lit, 9}}, [])
    end

    test "reduces to the false-branch on false" do
      assert {:vint, 9} ==
               Eval.eval({:bool_elim, {:bool_lit, false}, @const_motive, {:int_lit, 7}, {:int_lit, 9}}, [])
    end

    test "a concrete prim scrutinee drives the branch" do
      # bool_elim (3 == 3) _ 7 9  ==>  7
      scrut = {:prim, :eq, [{:int_lit, 3}, {:int_lit, 3}]}
      assert {:vint, 7} == Eval.eval({:bool_elim, scrut, @const_motive, {:int_lit, 7}, {:int_lit, 9}}, [])
    end

    test "a neutral scrutinee stays stuck as nbool_elim" do
      assert {:vneutral, {:nbool_elim, {:nvar, 0}, _m, _tt, _ff}} =
               Eval.eval({:bool_elim, {:var, 0}, @const_motive, {:int_lit, 7}, {:int_lit, 9}}, [
                 {:vneutral, {:nvar, 0}}
               ])
    end
  end

  describe "kernel typing" do
    setup do
      # var 0 : Bool
      %{ctx: Context.extend(Context.empty(), {:vbool_type})}
    end

    test "constant motive gives the branch result type", %{ctx: ctx} do
      t = {:bool_elim, {:var, 0}, @const_motive, {:int_lit, 7}, {:int_lit, 9}}
      assert {:ok, {:vint_type}} == Kernel.infer(ctx, t)
    end

    test "a dependent motive computes the result type per branch" do
      # motive = λb:Bool. bool_elim b (λ_.Type0) Int Bool
      #   true  -> Int, false -> Bool
      type_motive = {:lam, {:bool_type}, {:type, 0}}
      dep_motive =
        {:lam, {:bool_type},
         {:bool_elim, {:var, 0}, type_motive, {:int_type}, {:bool_type}}}

      # scrut = true: result type must be Int, and tt : Int, ff : Bool
      t = {:bool_elim, {:bool_lit, true}, dep_motive, {:int_lit, 5}, {:bool_lit, true}}
      assert {:ok, {:vint_type}} == Kernel.infer(Context.empty(), t)

      # scrut = false: result type must be Bool
      t2 = {:bool_elim, {:bool_lit, false}, dep_motive, {:int_lit, 5}, {:bool_lit, true}}
      assert {:ok, {:vbool_type}} == Kernel.infer(Context.empty(), t2)
    end

    test "rejects a non-Bool scrutinee", %{ctx: ctx} do
      t = {:bool_elim, {:int_lit, 3}, @const_motive, {:int_lit, 7}, {:int_lit, 9}}
      assert {:error, _} = Kernel.infer(ctx, t)
    end

    test "rejects a branch that disagrees with the motive", %{ctx: ctx} do
      # tt is a Bool but the constant motive says Int
      t = {:bool_elim, {:var, 0}, @const_motive, {:bool_lit, true}, {:int_lit, 9}}
      assert {:error, _} = Kernel.infer(ctx, t)
    end

    test "rejects a motive that is not Bool -> Type", %{ctx: ctx} do
      bad_motive = {:lam, {:int_type}, {:int_type}}
      t = {:bool_elim, {:var, 0}, bad_motive, {:int_lit, 7}, {:int_lit, 9}}
      assert {:error, _} = Kernel.infer(ctx, t)
    end
  end

  describe "conversion (stuck)" do
    test "identical stuck bool_elims are convertible" do
      t = {:bool_elim, {:var, 0}, @const_motive, {:int_lit, 7}, {:int_lit, 9}}
      assert Conv.conv?(t, t, [{:vneutral, {:nvar, 0}}], 1, Env.empty())
    end

    test "stuck bool_elims with different branches are NOT convertible" do
      t1 = {:bool_elim, {:var, 0}, @const_motive, {:int_lit, 7}, {:int_lit, 9}}
      t2 = {:bool_elim, {:var, 0}, @const_motive, {:int_lit, 7}, {:int_lit, 8}}
      refute Conv.conv?(t1, t2, [{:vneutral, {:nvar, 0}}], 1, Env.empty())
    end
  end

  describe "conversion faithfulness (SOUNDNESS: distinct branch types must NOT be equated)" do
    # A Bool-indexed type family `T(x) = bool_elim(b, λ_.Type, x, Bool)` stuck in a
    # neutral `b`. `T(Int)` and `T(Bool)` are distinct types (on b=true they are Int
    # and Bool). The tt branch is the bound parameter `{:var, 0}`; the false branch
    # binds nothing, so a fresh-binder prepend would mask it and equate the two.
    @family {:bool_elim, {:var, 1}, {:lam, {:bool_type}, {:type, 0}}, {:var, 0}, {:bool_type}}

    defp t_at(arg_value), do: Eval.eval(@family, [arg_value, {:vneutral, {:nvar, 0}}])

    test "T(Int) and T(Bool) are NOT convertible" do
      refute Conv.conv_values?(t_at({:vint_type}), t_at({:vbool_type}), 1, nil)
    end

    test "the kernel does not accept a T(Int) term at type T(Bool)" do
      ctx = Context.extend(Context.empty(), t_at({:vint_type}))
      assert {:error, _} = Kernel.check(ctx, {:var, 0}, t_at({:vbool_type}))
    end

    test "T(Int) is still convertible to itself (no false negative)" do
      assert Conv.conv_values?(t_at({:vint_type}), t_at({:vint_type}), 1, nil)
    end
  end

  describe "totality (SOUNDNESS: recursion inside a branch must be seen)" do
    # cond = (var0 == 0)
    defp cond, do: {:prim, :eq, [{:var, 0}, {:int_lit, 0}]}

    test "a NON-decreasing self-call hidden in a branch is NOT certified total" do
      selfcall = {:app, {:global, :bad}, {:var, 0}}

      body =
        {:lam, {:int_type},
         {:bool_elim, cond(), @const_motive, {:int_lit, 0}, selfcall}}

      # Before the certificate.ex fix, `calls?` misses the self-call inside the
      # branch, so `terminating?` wrongly returns true (certifying a loop).
      refute Certificate.terminating?(:bad, body, Env.empty())
    end

    test "a branch body with no self-call traverses without crashing and certifies" do
      body =
        {:lam, {:int_type},
         {:bool_elim, cond(), @const_motive, {:int_lit, 0}, {:int_lit, 1}}}

      assert Certificate.terminating?(:bad, body, Env.empty())
    end
  end
end
