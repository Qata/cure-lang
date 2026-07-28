defmodule Cure.Elab.LiteralProtocolTest do
  use ExUnit.Case, async: true

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
end
