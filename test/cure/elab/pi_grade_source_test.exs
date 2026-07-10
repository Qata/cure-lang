defmodule Cure.Elab.PiGradeSourceTest do
  @moduledoc """
  Slice 6: the def's **Pi binder is the single source of truth** for parameter
  quantities.

  Before this slice Cure stored each quantity twice and the two disagreed:
  `wrap_binders/3` hardcoded `ω` on every `:pi` and `:lam`, while the real vector
  lived in the def's `quantities`. An erased implicit or a demoted `where`-dict had
  `quantities: [:erased, …]` and a Pi/λ that said `ω` — the `ctor-spelling value
  dichotomy` class, one level up. Nothing re-checked the stored λ against the stored
  Π, so the lie was silent.

  Idris keeps the quantity on the Pi and nowhere else: `lcheck`'s `App` reads `rigf`
  off the callee's normalised type (`LinearCheck.idr:283`), and `eraseArgs` is a
  DERIVED projection of that type (`findErasedFrom`, `TTImp/Elab/Utils.idr:39-49`).

  This slice makes the stored Pi and λ carry the real grade, keeps them in agreement
  across `demote_unused_dicts/3`, and adds the assertion that would have caught the
  whole class: `Kernel.check` the final λ against the final Π before `Env.add_def`.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Eval, Context, Kernel}
  alias Cure.Elab.Program

  # Grades along a Π (or λ) spine, outermost first.
  defp pi_grades({:pi, g, _dom, cod}), do: [g | pi_grades(cod)]
  defp pi_grades(_), do: []

  defp lam_grades({:lam, g, _dom, body}), do: [g | lam_grades(body)]
  defp lam_grades(_), do: []

  @dict_src """
  mod C4
    interface Eqs(a)
      fn eqs(x: a, y: a) -> Bool
    implementation Eqs for Int
      fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    fn ignore({a: Type}, x: a) -> a where Eqs(a) = x
    fn same({a: Type}, x: a, y: a) -> Bool where Eqs(a) = eqs(x, y)
  end
  """

  describe "the Pi binder carries the real grade, matching quantities" do
    test "an erased implicit is erased on the Pi, not omega" do
      src = "mod I\n  fn id({a: Type}, x: a) -> a = x\nend\n"
      {:ok, env} = Program.elaborate(src)
      d = Env.get_def(env, :id)

      assert d.quantities == [:erased, :unrestricted]
      assert pi_grades(d.type) == d.quantities
      assert lam_grades(d.body) == d.quantities
    end

    test "a demoted where-dict is erased on BOTH the Pi and the lambda" do
      {:ok, env} = Program.elaborate(@dict_src)
      d = Env.get_def(env, :ignore)

      # {a} erased, x present, dict demoted to erased.
      assert d.quantities == [:erased, :unrestricted, :erased]
      assert pi_grades(d.type) == d.quantities,
             "Pi grades #{inspect(pi_grades(d.type))} must match quantities #{inspect(d.quantities)}"
      assert lam_grades(d.body) == d.quantities
    end

    test "a USED where-dict stays present on the Pi" do
      {:ok, env} = Program.elaborate(@dict_src)
      d = Env.get_def(env, :same)

      # {a} erased, x present, y present, dict USED -> present.
      assert d.quantities == [:erased, :unrestricted, :unrestricted, :unrestricted]
      assert pi_grades(d.type) == d.quantities
      assert lam_grades(d.body) == d.quantities
    end

    test "an all-explicit function is all-omega on the Pi (unchanged)" do
      src = "mod P\n  fn add(x: Int, y: Int) -> Int = x\nend\n"
      {:ok, env} = Program.elaborate(src)
      d = Env.get_def(env, :add)

      assert d.quantities == [:unrestricted, :unrestricted]
      assert pi_grades(d.type) == [:unrestricted, :unrestricted]
    end
  end

  describe "the stored lambda kernel-checks against the stored Pi" do
    # This is the assertion the slice adds, exercised from outside: whatever the
    # elaborator stored must be internally coherent — a λ whose grades match the type
    # it is stored under. If Pi and λ disagreed on any binder's grade, the graded
    # `Conv` (slice 2+3) would make this `Kernel.check` fail with `:grade_mismatch`.
    test "a demoted-dict def stores a coherent (λ : Π) pair" do
      {:ok, env} = Program.elaborate(@dict_src)
      d = Env.get_def(env, :ignore)

      ctx = Context.empty(env)
      assert :ok == Kernel.check(ctx, d.body, Eval.eval(d.type, Context.env(ctx)))
    end

    test "an erased-implicit def stores a coherent (λ : Π) pair" do
      {:ok, env} = Program.elaborate("mod I\n  fn id({a: Type}, x: a) -> a = x\nend\n")
      d = Env.get_def(env, :id)

      ctx = Context.empty(env)
      assert :ok == Kernel.check(ctx, d.body, Eval.eval(d.type, Context.env(ctx)))
    end
  end
end
