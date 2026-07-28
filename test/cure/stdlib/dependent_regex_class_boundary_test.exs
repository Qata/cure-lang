defmodule Cure.Stdlib.DependentRegexClassBoundaryTest do
  use ExUnit.Case, async: false

  setup_all do
    source = """
    mod RegexClassBoundaryRuntime
      use Std.Regex
      fn mixed_class(input: String) -> Option(Char) = parse_full(/[A-F\\d_]/i, input)
      fn unicode_class_digit(input: String) -> Option(Char) = parse_full(/[\\d]/u, input)
      fn class_not_digit(input: String) -> Option(Char) = parse_full(/[\\D]/, input)
      fn negated_class_digit(input: String) -> Option(Char) = parse_full(/[^\\d]/, input)
      fn class_horizontal_or_vertical(input: String) -> Option(Char) = parse_full(/[\\h\\v]/, input)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "escaped classes compose inside bracket classes with options and negation", %{runtime_module: module} do
    assert apply(module, :mixed_class, [[?b]]) == {:some, ?b}
    assert apply(module, :mixed_class, [[?7]]) == {:some, ?7}
    assert apply(module, :mixed_class, [[?_]]) == {:some, ?_}
    assert apply(module, :mixed_class, [[?z]]) == :none
    assert apply(module, :unicode_class_digit, [[?١]]) == {:some, ?١}
    assert apply(module, :class_not_digit, [[?a]]) == {:some, ?a}
    assert apply(module, :class_not_digit, [[?1]]) == :none
    assert apply(module, :negated_class_digit, [[?a]]) == {:some, ?a}
    assert apply(module, :negated_class_digit, [[?1]]) == :none
    assert apply(module, :class_horizontal_or_vertical, [[?\t]]) == {:some, ?\t}
    assert apply(module, :class_horizontal_or_vertical, [[?\n]]) == {:some, ?\n}
  end
end
