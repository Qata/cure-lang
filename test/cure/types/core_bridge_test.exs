defmodule Cure.Types.CoreBridgeTest do
  @moduledoc """
  The bridge covers the whole dependent-index grammar, so `Reduce` folds every
  computation in the kernel — including floats, negation, and applications that
  the old syntactic engine could not.
  """
  use ExUnit.Case, async: true
  alias Cure.Types.Reduce

  defp int(v), do: {:literal, [subtype: :integer], v}
  defp flt(v), do: {:literal, [subtype: :float], v}
  defp binop(op, l, r), do: {:binary_op, [operator: op], [l, r]}

  test "float arithmetic folds through the kernel" do
    assert {:literal, _, 3.5} = Reduce.normalize(binop(:+, flt(1.5), flt(2.0)))
    assert {:literal, _, 6.0} = Reduce.normalize(binop(:*, flt(2.0), flt(3.0)))
  end

  test "unary negation folds for ints and floats" do
    assert {:literal, _, -5} = Reduce.normalize({:unary_op, [operator: :-], [int(5)]})
    assert {:literal, _, -2.5} = Reduce.normalize({:unary_op, [operator: :-], [flt(2.5)]})
  end

  test "an application normalizes its arguments while staying applied" do
    ast = {:function_call, [name: "f"], [binop(:+, int(3), int(5)), {:variable, [], "n"}]}
    result = Reduce.normalize(ast)
    assert {:function_call, [name: "f"], [{:literal, _, 8}, {:variable, _, "n"}]} = result
  end

  test "integer remainder and inequality fold" do
    assert {:literal, _, 1} = Reduce.normalize(binop(:%, int(7), int(3)))
    assert {:literal, _, true} = Reduce.normalize(binop(:!=, int(1), int(2)))
  end

  test "an irreducible type former keeps its shape but folds its children" do
    ast = {:refinement_marker, [], [binop(:+, int(1), int(2))]}
    assert {:refinement_marker, [], [{:literal, _, 3}]} = Reduce.normalize(ast)
  end
end
