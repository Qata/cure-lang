defmodule Cure.Elab.TypeShadowingTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  test "R1a: explicit `use Std.Nat` + local `Nat = Zero|Suc` — local ctors cover the match" do
    src = """
    mod ExplicitShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn add(a: Nat, b: Nat) -> Nat = match a
        Zero() -> b
        Suc(m) -> Suc(add(m, b))
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R1 full: local `Nat = Z|S` fully shadows same-named imported ctors" do
    src = """
    mod FullShadow
      use Std.Nat
      type Nat = Z | S(Nat)
      fn two() -> Nat = S(S(Z()))
      fn pred(n: Nat) -> Nat = match n
        Z() -> Z()
        S(m) -> m
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  # R2 local half — the `imported_one`/`Std.Nat`-return half is restored in Task 8
  # (it needs qualified type-slot resolution).
  test "R2 (local half): local Zero/Suc still elaborate under `use Std.Nat`" do
    src = """
    mod PartialShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn local_one() -> Nat = Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R1 via transitive import: local `Nat` collides with a family reached only through `use Std.Vector` (no explicit `use Std.Nat`)" do
    src = """
    mod TransitiveShadow
      use Std.Vector
      type Nat = Zero | Suc(Nat)
      fn two() -> Nat = Suc(Suc(Zero()))
      fn pred(n: Nat) -> Nat = match n
        Zero() -> Zero()
        Suc(m) -> m
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  # Task 7 (value + pattern positions), isolated from the qualified TYPE slot
  # (Task 8): no local shadow, so `Nat`/`Std.Nat.Z`/`Std.Nat.S` resolve to the
  # imported family, exercising `elaborate_named_call` (expr) and `partition_arms`
  # (pattern) qualified-ctor resolution via bare-fallback. Full R3 (with `Std.Nat`
  # type slots + a local shadow) is added in Task 8.
  test "R3 (isolated): qualified ctor resolves in expression and pattern position" do
    src = """
    mod IsolatedEscape
      use Std.Nat
      fn two() -> Nat = Std.Nat.S(Std.Nat.Z())
      fn is_zero(n: Nat) -> Nat = match n
        Std.Nat.Z() -> Std.Nat.Z()
        Std.Nat.S(k) -> Std.Nat.S(Std.Nat.Z())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
end
