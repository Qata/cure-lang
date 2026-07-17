defmodule Cure.Stdlib.RefineTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a refined value carries kernel-checked evidence" do
    source = """
    mod ProofBackedRefinement
      use Std.Refine
      use Std.Proof.Math

      type PositiveNatural = {value: Nat | IsPositive(value)}

      fn one() -> PositiveNatural = refine(S(Z), PositiveSuccessor())

      fn value_is_positive(value: PositiveNatural) -> IsPositive(refined_value(value)) =
        refinement_proof(value)

    end
    """

    assert {:ok, _environment} = Program.elaborate(source)
  end

  test "a false refinement cannot be constructed without evidence" do
    source = """
    mod RejectedRefinement
      use Std.Refine
      use Std.Proof.Math

      type PositiveNatural = {value: Nat | IsPositive(value)}

      fn zero() -> PositiveNatural = refine(Z, PositiveSuccessor())
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end
end
