defmodule Cure.Stdlib.RegexBehaviorTest do
  use ExUnit.Case, async: false

  @regex :"Cure.Std.Regex"

  defp regex(pattern, flags \\ []) do
    apply(@regex, :literal, [to_charlist(pattern), to_charlist(flags)])
  end

  defp regex_match?(pattern, input, flags \\ []) do
    apply(@regex, :is_match, [regex(pattern, flags), to_charlist(input)])
  end

  defp full_match?(pattern, input, flags \\ []) do
    apply(@regex, :is_full_match, [regex(pattern, flags), to_charlist(input)])
  end

  describe "pure parser and matcher" do
    test "is_match searches like Elixir while is_full_match consumes the complete input" do
      assert regex_match?("abc", "abc")
      assert regex_match?("abc", "zabcd")
      refute regex_match?("abc", "ab")

      assert full_match?("abc", "abc")
      refute full_match?("abc", "zabc")
      refute full_match?("abc", "abcd")
    end

    test "alternation, grouping, and repetition" do
      assert regex_match?("(cat|dog)", "dog")
      refute regex_match?("(cat|dog)", "cow")
      assert regex_match?("[A-Z][a-z]*", "Cure")
      assert regex_match?("a+", "aaa")
      assert regex_match?("a*", "")
      assert regex_match?("colou?r", "color")
      assert regex_match?("colou?r", "colour")
    end

    test "dot excludes newline by default and includes it with s" do
      refute regex_match?(".", "\n")
      assert regex_match?(".", "\n", "s")
      assert regex_match?("...", "a\nb", "s")
    end

    test "anchors match the beginning and end of the input" do
      assert regex_match?("^abc$", "abc")
      refute regex_match?("^abc$", "xabc")
      refute regex_match?("^abc$", "abcx")
    end

    test "m lets anchors observe line boundaries in the suffix API" do
      assert regex_match?("a\n^b", "a\nb", "m")
      refute regex_match?("a\n^b", "a\nb")

      assert regex_match?("a$\nb", "a\nb", "m")
      refute regex_match?("a$\nb", "a\nb")
    end

    test "U and r select the ungreedy repeat ordering" do
      assert apply(@regex, :run, [regex("a*"), ~c"aaa"]) == [[], ~c"a", ~c"aa", ~c"aaa"]
      assert apply(@regex, :run, [regex("a*", "U"), ~c"aaa"]) == [~c"aaa", ~c"aa", ~c"a", []]
      assert apply(@regex, :run, [regex("a*", "r"), ~c"aaa"]) == [~c"aaa", ~c"aa", ~c"a", []]
    end

    test "character classes and ranges are matched" do
      assert regex_match?("[a-z]+", "hello")
      refute full_match?("[a-z]+", "hello!")
      assert regex_match?("[0-9][0-9]", "42")
      refute regex_match?("[0-9][0-9]", "4a")
    end

    test "caseless matching applies to literals and classes" do
      assert regex_match?("cure", "CURE", "i")
      refute regex_match?("cure", "CURE")
      assert regex_match?("[a-z]+", "CURE", "i")
      refute regex_match?("é", "É", "i")
      assert regex_match?("é", "É", "iu")
    end

    test "extended mode ignores layout and comments outside classes" do
      assert regex_match?("a b # ignored\n c", "abc", "x")
      assert regex_match?("[a b]", " ", "x")
      assert regex_match?("a\\ b", "a b", "x")
    end

    test "f prevents an unanchored match from starting after the first newline" do
      assert regex_match?("b", "a\nb")
      refute regex_match?("b", "a\nb", "f")
      assert regex_match?("a.*b", "a\nb", "fs")
    end

    test "u and E retain their Elixir behavior for Unicode Cure strings and pure values" do
      assert regex_match?("é", "café", "u")
      assert regex_match?("café", "CAFÉ", "iu")
      refute full_match?("\\w+", "josé")
      assert full_match?("\\w+", "josé", "u")
      refute regex_match?("\\d", "٣")
      assert regex_match?("\\d", "٣", "u")
      refute regex_match?("\\s", "\u00A0")
      assert regex_match?("\\s", "\u00A0", "u")
      assert regex_match?("cure", "cure", "E")
    end

    test "all Elixir modifier spellings are retained by the compiled value" do
      value = regex("a", "imsxurfUE")
      assert {:Configured, {:Literal, 97}, {:RawOptions, modifiers}} = value
      assert modifiers == ~c"imsxurfUE"
    end
  end
end
