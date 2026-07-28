defmodule Cure.Stdlib.DependentRegexModifierTest do
  use ExUnit.Case, async: false

  setup_all do
    source = """
    mod RegexModifierRuntime
      use Std.Regex

      fn caseless_exact() -> Option(Unit) = parse_full(/abc/i, "ABC")
      fn caseless_class() -> Option(Char) = parse_full(/[a-z]/i, "Q")
      fn sensitive_exact() -> Option(Unit) = parse_full(/abc/, "ABC")

      fn ordinary_dot_newline() -> Option(Char) = parse_full(/./, "\n")
      fn dotall_dot_newline() -> Option(Char) = parse_full(/./s, "\n")

      fn ascii_word_unicode_letter() -> Option(Char) = parse_full(/\\w/, "é")
      fn unicode_word_unicode_letter() -> Option(Char) = parse_full(/\\w/u, "é")
      fn ascii_digit_unicode_digit() -> Option(Char) = parse_full(/\\d/, "١")
      fn unicode_digit_unicode_digit() -> Option(Char) = parse_full(/\\d/u, "١")
      fn ascii_space_nbsp() -> Option(Char) = parse_full(/\\s/, " ")
      fn unicode_space_nbsp() -> Option(Char) = parse_full(/\\s/u, " ")
      fn unicode_caseless() -> Option(Unit) = parse_full(/é/iu, "É")

      fn extended_whitespace() -> Option(Unit) = parse_full(/a b/x, "ab")
      fn exported_identity() -> Option(Unit) = parse_full(/abc/E, "abc")

      fn alert_escape(input: String) -> Option(Unit) = parse_full(/\\a/, input)
      fn escape_escape(input: String) -> Option(Unit) = parse_full(/\\e/, input)
      fn form_feed_escape(input: String) -> Option(Unit) = parse_full(/\\f/, input)
      fn carriage_return_escape(input: String) -> Option(Unit) = parse_full(/\\r/, input)
      fn horizontal_escape(input: String) -> Option(Char) = parse_full(/\\h/, input)
      fn not_horizontal_escape(input: String) -> Option(Char) = parse_full(/\\H/, input)
      fn vertical_escape(input: String) -> Option(Char) = parse_full(/\\v/, input)
      fn not_vertical_escape(input: String) -> Option(Char) = parse_full(/\\V/, input)

      fn anchored_full(input: String) -> Option(Unit) = parse_full(/^abc$/, input)
      fn anchored_search(input: String) -> Option(Match(Unit)) = search(/^abc$/, input)
      fn multiline_anchored_search(input: String) -> Option(Match(Unit)) = search(/^abc$/m, input)
      fn ordinary_later_line_search(input: String) -> Option(Match(Unit)) = search(/abc/, input)
      fn firstline_search(input: String) -> Option(Match(Unit)) = search(/abc/f, input)

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn atom(char: Char) -> Regex(Char) = predicate(same(char))

      fn greedy_partition() -> Option(Tuple(String, String)) =
        parse_full(
          concatenate(
            captured(repeated_pattern(atom('a'), false)),
            captured(repeated_pattern(atom('a'), false))
          ),
          "aa"
        )

      fn lazy_partition() -> Option(Tuple(String, String)) =
        parse_full(
          concatenate(
            captured(repeated_pattern(atom('a'), true)),
            captured(repeated_pattern(atom('a'), false))
          ),
          "aa"
        )
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "i applies to literal characters and character ranges", %{runtime_module: module} do
    assert apply(module, :caseless_exact, []) == {:some, :unit}
    assert apply(module, :caseless_class, []) == {:some, ?Q}
    assert apply(module, :sensitive_exact, []) == :none
  end

  test "s controls whether dot consumes newline", %{runtime_module: module} do
    assert apply(module, :ordinary_dot_newline, []) == :none
    assert apply(module, :dotall_dot_newline, []) == {:some, ?\n}
  end

  test "u switches generic classes and case folding to Unicode", %{runtime_module: module} do
    assert apply(module, :ascii_word_unicode_letter, []) == :none
    assert apply(module, :unicode_word_unicode_letter, []) == {:some, ?é}
    assert apply(module, :ascii_digit_unicode_digit, []) == :none
    assert apply(module, :unicode_digit_unicode_digit, []) == {:some, ?١}
    assert apply(module, :ascii_space_nbsp, []) == :none
    assert apply(module, :unicode_space_nbsp, []) == {:some, 0xA0}
    assert apply(module, :unicode_caseless, []) == {:some, :unit}
  end

  test "x removes unescaped pattern whitespace before parsing", %{runtime_module: module} do
    assert apply(module, :extended_whitespace, []) == {:some, :unit}
  end

  test "E preserves direct behavior because Cure has no opaque pattern export", %{runtime_module: module} do
    assert apply(module, :exported_identity, []) == {:some, :unit}
  end

  test "PCRE control and horizontal/vertical whitespace escapes behave directly", %{runtime_module: module} do
    assert apply(module, :alert_escape, [[7]]) == {:some, :unit}
    assert apply(module, :escape_escape, [[27]]) == {:some, :unit}
    assert apply(module, :form_feed_escape, [[12]]) == {:some, :unit}
    assert apply(module, :carriage_return_escape, [[13]]) == {:some, :unit}

    assert apply(module, :horizontal_escape, [[9]]) == {:some, 9}
    assert apply(module, :horizontal_escape, [[0x2007]]) == {:some, 0x2007}
    assert apply(module, :horizontal_escape, [[?a]]) == :none
    assert apply(module, :not_horizontal_escape, [[?a]]) == {:some, ?a}

    assert apply(module, :vertical_escape, [[10]]) == {:some, 10}
    assert apply(module, :vertical_escape, [[0x2028]]) == {:some, 0x2028}
    assert apply(module, :vertical_escape, [[?a]]) == :none
    assert apply(module, :not_vertical_escape, [[?a]]) == {:some, ?a}
  end

  test "anchors use subject boundaries by default and line boundaries under m", %{runtime_module: module} do
    assert apply(module, :anchored_full, [~c"abc"]) == {:some, :unit}
    assert apply(module, :anchored_full, [~c"xabc"]) == :none
    assert apply(module, :anchored_search, [~c"x\nabc\ny"]) == :none

    assert apply(module, :multiline_anchored_search, [~c"x\nabc\ny"]) ==
             {:some, {:Match, :unit, ~c"x\n", ~c"abc", ~c"\ny"}}

    assert apply(module, :anchored_search, [~c"abc\n"]) ==
             {:some, {:Match, :unit, ~c"", ~c"abc", ~c"\n"}}
  end

  test "f restricts possible match starts to the first line", %{runtime_module: module} do
    assert apply(module, :ordinary_later_line_search, [~c"x\nabc"]) ==
             {:some, {:Match, :unit, ~c"x\n", ~c"abc", ~c""}}

    assert apply(module, :firstline_search, [~c"x\nabc"]) == :none

    assert apply(module, :firstline_search, [~c"xabc\nrest"]) ==
             {:some, {:Match, :unit, ~c"x", ~c"abc", ~c"\nrest"}}
  end

  test "greedy and lazy repetition preserve ordered Thompson preference", %{runtime_module: module} do
    assert apply(module, :greedy_partition, []) == {:some, {~c"aa", ~c""}}
    assert apply(module, :lazy_partition, []) == {:some, {~c"", ~c"aa"}}
  end
end
