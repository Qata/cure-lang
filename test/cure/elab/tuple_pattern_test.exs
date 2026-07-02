defmodule Cure.Elab.TuplePatternTest do
  @moduledoc """
  Parity row #4 (non-constructor patterns) — tuple/pair patterns. A Σ/pair is
  irrefutable, so a single `%[x, y] -> body` arm is a destructure, not a coverage
  problem. `try_tuple_match` lowers it to the already-supported projections:
  `body[x ↦ p.1, y ↦ p.2]` (Core `{:fst}`/`{:snd}` on the elaborated variable
  scrutinee), so no `{:vdata}` scrutinee and no new eliminator is needed. Scope:
  variable scrutinee, flat 2-tuple of variables/wildcards. Oracle
  `match/mt13_tuple_pattern` pins accept/accept parity.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a tuple pattern binds both projections and runs on the BEAM" do
    src = @nat <> "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    %[x, y] -> S(y)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.TuplePatternE2E", functions: [:f])

    # Runtime pair is a 2-tuple {a, b}; `.1`/`.2` are element(1)/element(2).
    assert apply(mod, :f, [{:Z, {:S, :Z}}]) == {:S, {:S, :Z}}
    assert apply(mod, :f, [{{:S, :Z}, :Z}]) == {:S, :Z}
  end

  test "the first projection is bound correctly" do
    src = @nat <> "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    %[x, y] -> x\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.TuplePatternFstE2E", functions: [:f])

    assert apply(mod, :f, [{:Z, {:S, :Z}}]) == :Z
  end

  test "a wildcard tuple element drops its projection" do
    src = @nat <> "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    %[_, y] -> y\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a plain constructor match is unaffected by the tuple path" do
    src = @nat <> "  fn f(n: Nat) -> Nat = match n\n    S(m) -> m\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end
end
