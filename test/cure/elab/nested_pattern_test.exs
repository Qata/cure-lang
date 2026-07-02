defmodule Cure.Elab.NestedPatternTest do
  @moduledoc """
  Parity row #3 (nested/deep patterns) — the single-nested-column slice. A match
  arm may carry a nested constructor sub-pattern (`S(S(m))`, `A(Z())`); it is
  lowered to nested *single-level* matches (`elaborate_match`'s
  `desugar_nested_arms`) so every level reuses the dependent match machinery
  (motives, index refinement, catch-all) and the kernel's own nesting `:case`.
  Oracle `match/mt07_nested_patterns` pins accept/accept parity.

  Scope: arms grouped by outer constructor, at most ONE nested argument column
  per group (others must be variables, substituted by their fresh binder).
  Multi-column nesting and a top-level catch-all mixed with nesting are rejected
  cleanly; deeper nesting is lowered on re-entry. No TCB change — pure surface
  lowering.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a two-deep nested pattern elaborates" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    S(Z()) -> Z()\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "nested pattern lowers to a correct runtime match on the BEAM" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    S(Z()) -> Z()\n    Z() -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedPatternE2E", functions: [:f])

    # S(S(m)) strips two successors: f(S(S(S(Z)))) = S(Z).
    assert apply(mod, :f, [{:S, {:S, {:S, :Z}}}]) == {:S, :Z}
    # S(S(m)) with m = Z: f(S(S(Z))) = Z.
    assert apply(mod, :f, [{:S, {:S, :Z}}]) == :Z
    # S(Z) branch and Z branch both yield Z.
    assert apply(mod, :f, [{:S, :Z}]) == :Z
    assert apply(mod, :f, [:Z]) == :Z
  end

  test "a variable sub-pattern in the nested column becomes an inner catch-all" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    S(k) -> k\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "single nested column with a sibling variable column (A(Z()) / A(S(k)) / B(y))" do
    src =
      @nat <>
        "  type T = A(Nat) | B(Nat)\n  fn g(t: T) -> Nat = match t\n    A(Z()) -> Z()\n    A(S(k)) -> k\n    B(y) -> y\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "triple nesting is handled by re-entry" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n    S(S(S(m))) -> m\n    S(S(Z())) -> Z()\n    S(Z()) -> Z()\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "COVERAGE: a non-exhaustive nested match is still rejected" do
    src = @nat <> "  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "multi-column nesting is a clean error (v1 limit)" do
    src =
      @nat <>
        "  type P = MkP(Nat, Nat)\n  fn h(p: P) -> Nat = match p\n    MkP(Z(), Z()) -> Z()\n    MkP(x, y) -> x\nend\n"

    assert {:error, {:unsupported_pattern, :multi_column_nesting}} = Program.elaborate(src)
  end
end
