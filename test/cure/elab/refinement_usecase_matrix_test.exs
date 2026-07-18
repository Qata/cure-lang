defmodule Cure.Elab.RefinementUsecaseMatrixTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # The end-to-end payoff of wiring refinement obligations into the auto-lemma
  # proof search: an author writes a value at a refinement type and the proof is
  # discovered from in-scope evidence, `@lemma`s, the conjunction/projection
  # candidate sources, or the positivity procedure — never by hand. Every case
  # here is kernel-rechecked, so acceptance means a real proof was built.

  defp accepts(src), do: assert({:ok, _env} = Program.elaborate(src))

  test "conjunctive range: both bounds in context build the conjunction (lemma intro)" do
    accepts("""
    mod RangeIntro
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      use Std.Proof.BooleanReflection
      fn clamp(x: Int, lo: IsTrue(0 <= x), hi: IsTrue(x <= 100)) -> {p: Int | 0 <= p and p <= 100} = x
    end
    """)
  end

  test "conjunctive range: a single conjunction hypothesis projects to one bound (elim)" do
    accepts("""
    mod RangeElim
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      use Std.Proof.BooleanReflection
      fn lower(x: Int, both: IsTrue(0 <= x and x <= 100)) -> {p: Int | 0 <= p} = x
    end
    """)
  end

  test "positivity of a product discharges from the two factors' positivity (lemma/procedure)" do
    accepts("""
    mod ProductPositive
      use Std.Nat
      use Std.Proof.Math
      fn prod(a: Nat, b: Nat, pa: IsPositive(a), pb: IsPositive(b)) -> {n: Nat | IsPositive(n)} = multiply(a, b)
    end
    """)
  end

  test "positivity of a successor discharges from the successor_is_positive lemma with no hypothesis" do
    accepts("""
    mod SuccessorPositive
      use Std.Nat
      use Std.Proof.Math
      fn positive_successor(k: Nat) -> {n: Nat | IsPositive(n)} = S(k)
    end
    """)
  end

  test "a refined value flows into the same refinement via its carried proof (projection)" do
    accepts("""
    mod RefinedPassthrough
      use Std.Nat
      use Std.Bool
      use Std.Proof.IntMath
      fn passthrough(v: {m: Int | m > 0}) -> {n: Int | n > 0} = v
    end
    """)
  end
end
