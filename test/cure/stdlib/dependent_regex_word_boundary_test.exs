defmodule Cure.Stdlib.DependentRegexWordBoundaryTest do
  use ExUnit.Case, async: false

  setup_all do
    source = """
    mod RegexWordBoundaryRuntime
      use Std.Regex

      fn cat() -> Regex(Unit) =
        discard_left(exactly('c'), discard_left(exactly('a'), exactly('t')))

      fn accent() -> Regex(Unit) = exactly('é')

      fn bounded(regex: Regex(Unit), unicode: Bool, negated: Bool) -> Regex(Unit) =
        discard_left(
          word_boundary(unicode, negated),
          discard_right(regex, word_boundary(unicode, negated))
        )

      fn ascii_word(input: String) -> Option(Match(Unit)) = search(bounded(cat(), false, false), input)
      fn interior(input: String) -> Option(Match(Unit)) = search(bounded(cat(), false, true), input)
      fn unicode_word(input: String) -> Option(Match(Unit)) = search(bounded(accent(), true, false), input)
      fn ascii_unicode_letter(input: String) -> Option(Match(Unit)) = search(bounded(accent(), false, false), input)
      fn class_backspace(input: String) -> Option(Char) = parse_full(one_of([8]), input)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "\\b observes the current search position and ASCII/Unicode word mode", %{runtime_module: module} do
    assert apply(module, :ascii_word, [~c"a cat!"]) ==
             {:some, {:Match, :unit, ~c"a ", ~c"cat", ~c"!"}}

    assert apply(module, :ascii_word, [~c"concatenate"]) == :none
    assert apply(module, :unicode_word, [[?\s, ?é, ?\s]]) ==
             {:some, {:Match, :unit, ~c" ", ~c"é", ~c" "}}
    assert apply(module, :ascii_unicode_letter, [[?\s, ?é, ?\s]]) == :none
  end

  test "\\B is the complement and \\b inside a class is backspace", %{runtime_module: module} do
    assert apply(module, :interior, [~c"scatx"]) ==
             {:some, {:Match, :unit, ~c"s", ~c"cat", ~c"x"}}

    assert apply(module, :class_backspace, [[8]]) == {:some, 8}
  end
end
