defmodule Cure.Stdlib.ProofMathTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "positive multiplication is proved by reusable Cure evidence" do
    source = """
    mod ProofMathConsumer
      use Std.Proof.Math

      fn two_is_positive() -> IsPositive(S(S(Z))) = PositiveSuccessor()

      fn four_is_positive() -> IsPositive(multiply(S(S(Z)), S(S(Z)))) =
        multiplying_positive_numbers_is_positive(two_is_positive(), two_is_positive())
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "positivity decisions carry checked evidence" do
    source = """
    mod ProofMathDecisionConsumer
      use Std.Proof.Math

      fn successor_is_positive(natural: Nat) -> IsPositive(S(natural)) =
        match decide_is_positive(S(natural))
          Yes(proof) -> proof
          No(disproof) -> match disproof(PositiveSuccessor())
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "less-than-or-equal proofs compose transitively" do
    source = """
    mod ProofMathOrderConsumer
      use Std.Proof.Math

      fn compose(
        {left: Nat},
        {middle: Nat},
        {right: Nat},
        first: IsLessThanOrEqual(left, middle),
        second: IsLessThanOrEqual(middle, right)
      ) -> IsLessThanOrEqual(left, right) =
        less_than_or_equal_is_transitive(first, second)
    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end
end
