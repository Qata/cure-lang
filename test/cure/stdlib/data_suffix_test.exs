defmodule Cure.Stdlib.DataSuffixTest do
  @moduledoc """
  The strict-suffix relation underlying `Std.Parse`: `Same` proves an unchanged
  remainder, while `Drop` changes the strictness index to `True` and extends the
  original input by exactly one head.
  """

  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @foundation """
    use Std.Bool
    use Std.List

    type Consumed(a: Type) indices (strict: Bool, rem: List(a), orig: List(a))
      Same : (xs: List(a)) -> Consumed(a, False, xs, xs)
      Drop : (head: a) -> Consumed(a, strict, rem, orig) -> Consumed(a, True, rem, Cons(head, orig))

    fn trans({a: Type}, {left: Bool}, {right: Bool}, {orig: List(a)}, {mid: List(a)}, {rem: List(a)}, first: Consumed(a, left, mid, orig), second: Consumed(a, right, rem, mid)) -> Consumed(a, `or`(left, right), rem, orig) =
      match first
        Same(_) -> second
        Drop(head, previous) -> Drop(head, trans(previous, second))
  """

  defp verdict(definitions) do
    case Program.elaborate("mod SuffixProbe\n#{@foundation}#{definitions}\nend\n") do
      {:ok, _env} -> :accept
      {:error, _reason} -> :reject
    end
  end

  test "Same proves that the remainder is the original input" do
    assert verdict("fn p({a: Type}, xs: List(a)) -> Consumed(a, False, xs, xs) = Same(xs)") == :accept
  end

  test "Drop proves a strict suffix after discarding one head" do
    definition = """
      fn p({a: Type}, head: a, tail: List(a)) -> Consumed(a, True, tail, Cons(head, tail)) =
        Drop(head, Same(tail))
    """

    assert verdict(definition) == :accept
  end

  test "Same cannot fabricate a strict-consumption witness" do
    assert verdict("fn bad({a: Type}, xs: List(a)) -> Consumed(a, True, xs, xs) = Same(xs)") == :reject
  end

  test "Drop cannot claim an unrelated remainder" do
    definition = """
      fn bad({a: Type}, x: a, ys: List(a), zs: List(a)) -> Consumed(a, True, zs, Cons(x, ys)) =
        Drop(x, Same(ys))
    """

    assert verdict(definition) == :reject
  end

  test "trans composes two strict drops and preserves the final remainder" do
    definition = """
      fn p({a: Type}, x: a, y: a, tail: List(a)) -> Consumed(a, True, tail, Cons(x, Cons(y, tail))) =
        trans(Drop(x, Same(Cons(y, tail))), Drop(y, Same(tail)))
    """

    assert verdict(definition) == :accept
  end

  test "trans with Same on the left preserves the second proof's strictness" do
    definition = """
      fn p({a: Type}, x: a, tail: List(a)) -> Consumed(a, True, tail, Cons(x, tail)) =
        trans(Same(Cons(x, tail)), Drop(x, Same(tail)))
    """

    assert verdict(definition) == :accept
  end

end
