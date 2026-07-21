defmodule Cure.Stdlib.DependentRegexShapeTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @shape_source File.read!(Path.expand("../../../lib/std/regex.cure", __DIR__))

  test "ShapeCode and Sem elaborate as a genuine large elimination" do
    assert {:ok, _env} = Program.elaborate(@shape_source)
  end

  test "Sem reduces nested pair, list, and unit codes definitionally" do
    source = """
    mod RegexShapeUse
      use Std.Regex

      fn nested(value: Char) -> Sem(PairC(CharC, ListC(UnitC))) =
        %[value, [(), ()]]
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "Sem rejects a value from the wrong computed branch" do
    source = """
    mod RegexShapeWrong
      use Std.Regex

      fn wrong() -> Sem(CharC) = true
    end
    """

    assert {:error, _diagnostic} = Program.elaborate(source)
  end
end
