defmodule Cure.Elab.LiteralProtocolTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Cure.Core.Env
  alias Cure.Elab.Program

  test "natural and integer protocols dispatch from the contextual result type" do
    source = """
    mod LiteralDispatch
      type NaturalBox = NaturalBoxValue(Nat)
      type IntegerBox = IntegerBoxValue(Int)

      implementation ExpressibleByNaturalLiteral for NaturalBox
        fn from_natural_literal(value: Nat) -> LiteralResult(NaturalBox) =
          LiteralValue(NaturalBoxValue(value))

      implementation ExpressibleByIntegerLiteral for IntegerBox
        fn from_integer_literal(value: Int) -> LiteralResult(IntegerBox) =
          LiteralValue(IntegerBoxValue(value))

      fn natural() -> NaturalBox = 7
      fn integer_fallback() -> IntegerBox = 9
      fn negative_integer() -> IntegerBox = -4
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ctor, :"LiteralDispatch#NaturalBoxValue", [{:nat_lit, 7}]} = Env.get_def(env, :natural).body

    assert {:ctor, :"LiteralDispatch#IntegerBoxValue", [{:int_lit, 9}]} =
             Env.get_def(env, :integer_fallback).body

    assert {:ctor, :"LiteralDispatch#IntegerBoxValue", [{:int_lit, -4}]} =
             Env.get_def(env, :negative_integer).body
  end

  test "Char accepts in-range natural literals in either operator position" do
    source = """
    mod ContextualCharLiteral
      fn value() -> Char = 12
      fn right(char: Char) -> Bool = char == 12
      fn left(char: Char) -> Bool = 12 == char
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "Char rejects a natural literal beyond the Unicode bound" do
    source = """
    mod InvalidContextualCharLiteral
      fn invalid() -> Char = 1114112
    end
    """

    assert {:error, error} = Program.elaborate(source)

    assert {:literal_out_of_range, :from_natural_literal, 1_114_112, _expected} =
             Program.semantic_error(error)
  end

  test "a bare numeral continues to default to Int" do
    assert {:ok, env} = Program.elaborate("mod BareLiteral\n  fn value() = 23\n")
    assert {:int_lit, 23} = Env.get_def(env, :value).body
  end

  test "a type conforming to both protocols routes negatives exclusively through integer" do
    source = """
    mod CoherentLiteralDispatch
      type Dual = FromNatural(Nat) | FromInteger(Int)

      implementation ExpressibleByNaturalLiteral for Dual
        fn from_natural_literal(value: Nat) -> LiteralResult(Dual) = LiteralValue(FromNatural(value))

      implementation ExpressibleByIntegerLiteral for Dual
        fn from_integer_literal(value: Int) -> LiteralResult(Dual) = LiteralValue(FromInteger(value))

      fn positive() -> Dual = 3
      fn negative() -> Dual = -3
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ctor, :"CoherentLiteralDispatch#FromNatural", [{:nat_lit, 3}]} = Env.get_def(env, :positive).body
    assert {:ctor, :"CoherentLiteralDispatch#FromInteger", [{:int_lit, -3}]} = Env.get_def(env, :negative).body
  end

  test "a user-defined conversion can reject a literal at compile time" do
    source = """
    mod RejectingLiteral
      type Tiny = TinyValue(Nat)

      implementation ExpressibleByNaturalLiteral for Tiny
        fn from_natural_literal(value: Nat) -> LiteralResult(Tiny) = InvalidLiteral()

      fn invalid() -> Tiny = 4
    end
    """

    assert {:error, error} = Program.elaborate(source)
    assert {:literal_out_of_range, :from_natural_literal, 4, _} = Program.semantic_error(error)
  end

  property "Nat, Int, Char, Bounded, and a custom type accept generated in-domain literals" do
    check all(
            natural <- integer(0..64),
            signed <- integer(-64..64),
            char <- integer(0..127),
            bound <- integer(1..32),
            bounded <- integer(0..(bound - 1)),
            max_runs: 8
          ) do
      source = """
      mod GeneratedLiteralDomains
        type Custom = CustomValue(Nat)

        implementation ExpressibleByNaturalLiteral for Custom
          fn from_natural_literal(value: Nat) -> LiteralResult(Custom) = LiteralValue(CustomValue(value))

        fn natural() -> Nat = #{natural}
        fn signed() -> Int = #{signed}
        fn char() -> Char = #{char}
        fn bounded() -> Bounded(#{bound}) = #{bounded}
        fn custom() -> Custom = #{natural}
      end
      """

      assert {:ok, _env} = Program.elaborate(source)
    end
  end

  property "generated out-of-domain Bounded literals are rejected with their value and bound" do
    check all(bound <- integer(0..32), excess <- integer(0..32), max_runs: 8) do
      value = bound + excess
      source = "mod GeneratedBoundFailure\n  fn invalid() -> Bounded(#{bound}) = #{value}\n"

      assert {:error, error} = Program.elaborate(source)
      assert {:bounded_lit_out_of_range, ^value, ^bound} = Program.semantic_error(error)
    end
  end
end
