defmodule Cure.Elab.CatchallPatternTest do
  @moduledoc """
  Parity row #4 (non-constructor patterns in dependent position) — the
  variable/wildcard **catch-all** slice. A `match` arm whose pattern is a bare
  variable (`x -> …`) or wildcard (`_ -> …`) covers every constructor not
  explicitly matched, binding the scrutinee (Idris/Lean variable-pattern
  coverage). Oracle `match/mt06_var_catchall` pins accept/accept parity.

  Implemented purely in the elaborator (E): each un-matched constructor is
  reconstructed as `cname(fresh…)`, the catch-all's name is substituted by that
  reconstruction, and the branch routes through the ordinary matched-branch path
  — so index inversion and goal refinement still apply and an unsound catch-all
  body is still rejected by the kernel. No TCB change.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @dep_hdr "mod M\n  type Dec = DDec | DCau\n  type G indices (d: Dec)\n    mkd : G(DDec)\n    seqg : G(d1) -> G(d2) -> G(DCau)\n"

  test "non-dependent variable catch-all covers all un-matched constructors" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  fn f(c: Color) -> Color = match c\n    Red() -> Blue()\n    other -> other\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "wildcard catch-all elaborates" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  fn f(c: Color) -> Color = match c\n    Red() -> Blue()\n    _ -> Red()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "catch-all alone (no explicit constructor arms) binds the scrutinee" do
    src = "mod M\n  type Color = Red | Green | Blue\n  fn id2(c: Color) -> Color = match c\n    x -> x\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "dependent catch-all reconstructs each constructor at its refined index" do
    # `x -> x`: the seqg branch refines `d := DCau`, and the reconstructed `x`
    # (= seqg(…) : G(DCau)) must match the branch-refined goal G(DCau).
    src = @dep_hdr <> "  fn f({d: Dec}, s: G(d)) -> G(d) = match s\n    mkd() -> mkd()\n    x -> x\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "SOUNDNESS: catch-all covering a reachable constructor at the wrong index is rejected" do
    # Goal is the CONCRETE G(DDec). The catch-all covers the reachable `seqg`
    # branch, where the reconstructed value has type G(DCau). DCau ≢ DDec, so the
    # branch's conversion must reject — the catch-all does not bypass the kernel.
    src = @dep_hdr <> "  fn f({d: Dec}, s: G(d)) -> G(DDec) = match s\n    mkd() -> mkd()\n    x -> x\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "two catch-alls in one match are rejected" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  fn f(c: Color) -> Color = match c\n    x -> x\n    y -> y\nend\n"

    assert {:error, {:duplicate_default_pattern, _}} = Program.elaborate(src)
  end

  test "the catch-all runs on the BEAM, covering every un-matched constructor" do
    src =
      "mod M\n  type Color = Red | Green | Blue\n  type Nat = Z | S(Nat)\n  fn tag(c: Color) -> Nat = match c\n    Red() -> Z()\n    other -> S(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.CatchAllPatternE2E", functions: [:tag])

    assert apply(mod, :tag, [:Red]) == :Z
    assert apply(mod, :tag, [:Green]) == {:S, :Z}
    assert apply(mod, :tag, [:Blue]) == {:S, :Z}
  end

  # Boundary for parity #3 (nested/deep patterns → decision-tree lowering, not
  # yet implemented): a nested constructor sub-pattern must yield a CLEAN error,
  # never crash `constructor_pattern` with a raw no-clause exception.
  test "a nested constructor sub-pattern is a clean error, not a crash" do
    src =
      "mod M\n  type Nat = Z | S(Nat)\n  fn f(n: Nat) -> Nat = match n\n    S(S(m)) -> m\n    S(Z()) -> Z()\n    Z() -> Z()\nend\n"

    assert {:error, {:unsupported_pattern, :nested_constructor_arg}} = Program.elaborate(src)
  end
end
