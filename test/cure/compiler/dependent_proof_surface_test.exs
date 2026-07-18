defmodule Cure.Compiler.DependentProofSurfaceTest do
  use ExUnit.Case, async: false

  test "surface Equivalent and reflexive elaborate through the dependent compiler" do
    src = """
    mod ProofReflOnly
      type Nat = Z | S(Nat)
      fn zero_refl() -> Equivalent(Nat, Z, Z) = reflexive(Z)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.ProofReflOnly"
    # `reflexive` is now a genuine inductive constructor with an ERASED witness, so
    # it lowers to the canonical nullary ctor tag `:reflexive` (retiring the
    # faking-era `:cure_refl` sentinel — spec 2026-07-04-identity-type-as-inductive).
    assert apply(mod, :zero_refl, []) == :reflexive
  end

  test "surface rewrite proves plus right identity for Nat" do
    src = """
    mod ProofPlusZero
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
        Z() -> reflexive(Z)
        S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.ProofPlusZero"
    # Both branches reduce to the erased inductive `reflexive` ctor tag (see above).
    assert apply(mod, :plus_zero_right, [:Z]) == :reflexive
    assert apply(mod, :plus_zero_right, [{:S, :Z}]) == :reflexive
  end

  test "reflexive is rejected when equality endpoints are not definitionally equal" do
    src = """
    mod ProofBadRefl
      type Nat = Z | S(Nat)
      fn bad() -> Equivalent(Nat, Z, S(Z)) = reflexive(Z)
    end
    """

    # `reflexive(Z)` proves `Equivalent(Nat, Z, Z)`, which the kernel's
    # conversion check refuses to unify with the declared goal
    # `Equivalent(Nat, Z, S(Z))`. The sole (dependent) pipeline surfaces that as
    # a `conversion_failure` rather than the classic `dependent_type_error`.
    assert {:error, {:codegen_error, {:conversion_failure, _lhs, _rhs}}} =
             Cure.Compiler.compile_and_load(src, emit_events: false)
  end

  test "rewrite … in parses with `in` on the next line (multi-line chain)" do
    # A `rewrite … in …` chain may place `in` at the start of the next line at the
    # same indentation. `rewrite` always requires `in`, so the parser skips the
    # intervening newline to find it (regression: previously `:expected :in got :newline`).
    src = """
    mod ProofRewriteMultiline
      type Nat = Z | S(Nat)
      fn plus(m: Nat, n: Nat) -> Nat = match m
        Z() -> n
        S(k) -> S(plus(k, n))
      fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
        Z() -> reflexive(Z)
        S(k) ->
          rewrite plus_zero_right(k)
          in reflexive(S(k))
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :plus_zero_right, [{:S, {:S, :Z}}]) == :reflexive
  end
end
