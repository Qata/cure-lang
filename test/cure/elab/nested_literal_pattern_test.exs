defmodule Cure.Elab.NestedLiteralPatternTest do
  use ExUnit.Case, async: true

  defp compile(source) do
    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    module
  end

  test "literal heads in list patterns remain refutable" do
    module =
      compile("""
      mod NestedLiteralListPattern
        fn classify(input: String) -> Int = match input
          ['[' | _] -> 1
          ['x' | _] -> 2
          _ -> 3
      end
      """)

    assert apply(module, :classify, [~c"[abc"]) == 1
    assert apply(module, :classify, [~c"xyz"]) == 2
    assert apply(module, :classify, [~c"abc"]) == 3
    assert apply(module, :classify, [[]]) == 3
  end

  test "literal columns compose with later nested columns and guards" do
    module =
      compile("""
      mod NestedLiteralMultipleColumns
        fn classify(input: String) -> Int = match input
          ['a', 'b' | _] when true -> 1
          ['a', _ | _] -> 2
          _ -> 3
      end
      """)

    assert apply(module, :classify, [~c"abz"]) == 1
    assert apply(module, :classify, [~c"acz"]) == 2
    assert apply(module, :classify, [~c"zab"]) == 3
  end

  test "literal list patterns remain refutable inside an outer constructor" do
    module =
      compile("""
      mod NestedLiteralConstructorPattern
        type Parsed = Parsed(Int, String) | Invalid

        fn classify(value: Parsed) -> Int = match value
          Parsed(_, ['*' | _]) -> 1
          Parsed(_, ['+' | _]) -> 2
          _ -> 3

        fn star() -> Int = classify(Parsed(0, "*tail"))
        fn plus() -> Int = classify(Parsed(0, "+tail"))
        fn other() -> Int = classify(Parsed(0, "tail"))
      end
      """)

    assert apply(module, :star, []) == 1
    assert apply(module, :plus, []) == 2
    assert apply(module, :other, []) == 3
  end
end
