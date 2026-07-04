defmodule Cure.Elab.Ledger10HofInferTest do
  use ExUnit.Case, async: false
  alias Cure.Elab.{Program, Emit}

  # Ledger #10 — dependent higher-order inference (`try_lambda_meta_pi`).
  #
  # A lambda passed where the expected Π domain's CODOMAIN still bears a
  # metavariable — `g : (n: Nat) -> P(n)` with `P` an implicit `(Nat) -> Type` —
  # cannot be inferred standalone. The elaborator binds the parameter, INFERS the
  # body, and Miller-unifies the reconstructed Π against the expected one, solving
  # the codomain metavariable UNDER the binder (`?P(n) := λn. body_ty`). Until
  # higher-order pattern unification (`Unify.mabs`) and this path landed, such a
  # program was rejected (see unsolved_implicit_no_crash_test's note). These tests
  # pin the accept side and check the solved `P` is applied correctly at runtime.

  # Constant codomain: body `Suc(n) : Nat` for all n ⇒ P := λn. Nat.
  @const_src """
  mod MConst
    type Nat = Zero | Suc(Nat)
    fn hof({P: (Nat) -> Type}, g: (n: Nat) -> P(n)) -> P(Zero) = g(Zero)
    fn mk() -> Nat = hof(fn (n) -> Suc(n) end)
    fn one() -> Nat = Suc(Zero)
  end
  """

  # Dependent codomain: body `refl(n) : Eq(Nat, n, n)` ⇒ P := λn. Eq(Nat, n, n).
  # The pattern var n must be abstracted INSIDE the Eq — the mabs Eq clause,
  # exercised here through the full elaborator rather than a unit unify call.
  @dep_src """
  mod MDep
    type Nat = Zero | Suc(Nat)
    fn hof({P: (Nat) -> Type}, g: (n: Nat) -> P(n)) -> P(Zero) = g(Zero)
    fn mk() -> Eq(Nat, Zero, Zero) = hof(fn (n) -> refl(n) end)
    fn direct() -> Eq(Nat, Zero, Zero) = refl(Zero)
  end
  """

  test "constant codomain P := λn. Nat is inferred, accepted, and runs" do
    assert {:ok, env} = Program.elaborate(@const_src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.Ledger10Const", functions: [:mk, :one, :hof])

    # hof solves P := λn.Nat, returns g(Zero) = (λn. Suc n)(Zero) = Suc Zero.
    assert apply(mod, :mk, []) == apply(mod, :one, [])
  end

  test "dependent codomain P := λn. Eq(Nat,n,n) is inferred, accepted, and runs" do
    assert {:ok, env} = Program.elaborate(@dep_src)

    {:ok, mod} =
      Emit.compile_and_load(env, module: :"Cure.Ledger10Dep", functions: [:mk, :direct, :hof])

    # P := λn. Eq(Nat,n,n); return P(Zero) = Eq(Nat,Zero,Zero); g(Zero) = refl(Zero).
    assert apply(mod, :mk, []) == apply(mod, :direct, [])
  end
end
