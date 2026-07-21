defmodule Cure.Stdlib.DependentRegexCoreTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "Pattern constructors compute their result shapes" do
    source = """
    mod RegexCoreShapes
      use Std.Regex

      fn any(char: Char) -> Bool = true

      fn atom() -> Pattern(CharC) = PatternPredicate(any)
      fn nullable() -> Pattern(UnitC) = PatternEmpty()
      fn pair() -> Pattern(PairC(CharC, UnitC)) = PatternConcat(atom(), nullable())
      fn branch() -> Pattern(ChoiceC(CharC, UnitC)) = PatternAlternate(atom(), nullable())
      fn many() -> Pattern(ListC(CharC)) = PatternRepeat(atom())
      fn capture() -> Pattern(StringC) = PatternGroup(atom())
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "Pattern rejects an incorrect constructor index" do
    source = """
    mod RegexCoreWrong
      use Std.Regex

      fn wrong() -> Pattern(CharC) = PatternEmpty()
    end
    """

    assert {:error, _diagnostic} = Program.elaborate(source)
  end

  test "Regex combinators compute user result types" do
    source = """
    mod RegexTypedShapes
      use Std.Regex

      fn any(char: Char) -> Bool = true
      fn char() -> Regex(Char) = predicate(any)
      fn pair() -> Regex(Tuple(Char, Unit)) = concatenate(char(), empty())
      fn branch() -> Regex(Choice(Char, Unit)) = alternate(char(), empty())
      fn many() -> Regex(List(Char)) = repeat(char())
      fn count(chars: List(Char)) -> Int = match chars
        [] -> 0
        [_ | rest] -> 1 + count(rest)
      fn counted() -> Regex(Int) = map(many(), count)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
