# test/cure/compiler/macro_error_floor_test.exs
defmodule Cure.Compiler.MacroErrorFloorTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Errors}

  # Parse a source expected to fail, return its error list.
  defp errors_of(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:error, errors} = Parser.parse(tokens, emit_events: false)
    errors
  end

  test "a macro-use literal mismatch renders a friendly diagnostic naming the macro + what it expected" do
    # `say hello` is the rule; `say goodbye` mismatches on the literal segment.
    errors =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say goodbye\n")

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    # A DIAGNOSTIC, not a raw tuple: names the macro, what it expected, what it got.
    assert rendered =~ "say"
    assert rendered =~ "hello"
    assert rendered =~ "goodbye"
    refute rendered =~ ":macro_use_mismatch"
    refute rendered =~ ":at_segment"
  end

  test "a macro-use mismatch against a bare keyword at end-of-line stays on one line" do
    # `say` used with nothing after it: the mismatch token is the newline that
    # ends the statement. The diagnostic must describe it in words ("end of
    # line"), not splice the raw newline byte into the "found ..." clause --
    # doing so breaks format_diagnostic's single-line `| message` convention
    # and visually corrupts the error (a blank continuation line with no `|`
    # prefix, and the closing "(at column N)" left dangling on its own line).
    errors =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say\n  fn g() = 1\n")

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    # Every physical line of the diagnostic must be non-empty: no bare `\n`
    # was ever spliced into the message body.
    assert Enum.all?(String.split(rendered, "\n"), &(&1 != "")),
           "diagnostic should not contain an embedded raw newline:\n#{rendered}"

    refute rendered =~ "found `\n"
    assert rendered =~ "end of line"
  end

  test "a macro-use mismatch against a bare keyword at true end-of-block names the dedent" do
    # `say` as the very last thing in its block, with nothing after it: the
    # closing `dedent` token (whose value is a bare indentation-level
    # integer, not source text) is the mismatch token. It must be named in
    # words, not rendered as the meaningless raw integer.
    errors = errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say")

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    assert rendered =~ "found `a dedent`"
  end

  test "a macro-use mismatch against the `nil` keyword names it, not an empty string" do
    # `nil` is lexed as %Token{type: nil, value: nil} (unlike every other
    # keyword, which lexes as {:keyword, atom}) -- so it carries no source
    # text in either field for macro_got_desc's generic fallbacks to find.
    # Without a dedicated clause it renders as `found ``` (empty backticks).
    errors =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say nil\n")

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    assert rendered =~ "found `nil`"
    refute rendered =~ "found ``"
  end

  test "a macro-use mismatch against a char literal names the character, not its codepoint" do
    # A `:char` token's value is the decoded Unicode codepoint (e.g. 97 for
    # 'a'), not its source spelling. Without a dedicated clause,
    # macro_got_desc's generic `to_string(v)` fallback renders the bare
    # integer -- `found `97`` -- which doesn't look like anything the user
    # typed.
    errors =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say 'a'\n")

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    assert rendered =~ "found `'a'`"
    refute rendered =~ "found `97`"
  end

  test "a macro-use mismatch never splices a raw control character into the diagnostic" do
    # The structural-token (newline/indent/dedent) and char-literal fixes
    # above special-case specific token *types*, but the real invariant is
    # about *content*: any token whose decoded value happens to contain a
    # raw control character must not corrupt format_diagnostic's single-line
    # `| message` convention. Two content-bearing token kinds reach this
    # through the generic to_string(v) (string) and the dedicated :char
    # clause (char) fallbacks -- both must come out escaped, not raw.
    string_with_escape =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say \"a\\nb\"\n")

    string_mismatch =
      Enum.find(string_with_escape, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))

    assert string_mismatch, "expected a :macro_use_mismatch error"
    rendered_string = Errors.format_error(string_mismatch, "f.cure")

    # A well-formed 3-line diagnostic (severity, location, message). A raw
    # embedded newline breaks one non-empty line into two non-empty lines --
    # "all lines non-empty" would NOT catch that -- so assert the line count
    # directly.
    assert length(String.split(rendered_string, "\n")) == 3,
           "a string literal's embedded newline must not corrupt the diagnostic:\n#{rendered_string}"

    char_newline =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say '\\n'\n")

    char_mismatch =
      Enum.find(char_newline, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))

    assert char_mismatch, "expected a :macro_use_mismatch error"
    rendered_char = Errors.format_error(char_mismatch, "f.cure")

    assert length(String.split(rendered_char, "\n")) == 3,
           "a char literal's raw newline value must not corrupt the diagnostic:\n#{rendered_char}"
  end

  test "the hole-kind and nothing-more mismatch renders are total and grammatical" do
    # `{:hole_kind, _}` and `:nothing_more` are not reachable through today's
    # match_segments/4 (a `{:hole, _}` segment never fails to match, so the
    # parser's own call site only ever supplies `{:literal, _}`) -- confirmed
    # by reading match_segments/4 in parser.ex. Exercise format_error/2 on
    # these shapes directly so the render arms (and `article/1`'s vowel
    # check) stay covered and total even though no live input reaches them
    # today; the tuple shape itself is part of format_error's contract.
    assert Errors.format_error({:macro_use_mismatch, "every", {:hole_kind, "Int"}, "x", 1, 1}, "f") =~
             "expected an Int here"

    assert Errors.format_error(
             {:macro_use_mismatch, "every", {:hole_kind, "Duration"}, "x", 1, 1},
             "f"
           ) =~ "expected a Duration here"

    assert Errors.format_error({:macro_use_mismatch, "every", :nothing_more, "x", 1, 1}, "f") =~
             "has no more to match here"
  end

  test "a malformed hole in a macro definition renders a diagnostic explaining the hole syntax" do
    # Missing the closing `>` — the milestone-1 :malformed_hole path.
    errors = errors_of("macro Bad\n  syntax every <t: Duration becomes x\n")

    mh = Enum.find(errors, &match?({:malformed_hole, _, _}, &1))
    assert mh, "expected a :malformed_hole error"

    rendered = Errors.format_error(mh, "bad.cure")
    assert rendered =~ "hole"
    assert rendered =~ "<name: Kind>"
    refute rendered =~ ":malformed_hole"
  end

  test "a macro-use mismatch against a structured-value token (regex) yields a diagnostic, not a crash" do
    # A :regex token's value is a `{body, flags}` TUPLE; match_segments'
    # `{:lit, w}` literal comparison used `to_string(tok.value)`, which RAISES
    # on a tuple — so `say ~r/foo/` (rule `say hello`) crashed the parser
    # instead of producing a mismatch. Must yield the friendly diagnostic.
    errors =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say ~r/foo/\n")

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    assert rendered =~ "say"
    assert rendered =~ "regex"
  end

  test "a macro-use mismatch against an interpolated string (list value) yields a diagnostic, not a crash" do
    # A :string_interpolation token's value is a LIST of parts; the same
    # `to_string(tok.value)` path raises on a list. `\#{name}` keeps the
    # interpolation literal in the Cure source (Elixir would otherwise expand it).
    errors =
      errors_of("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say \"hi \#{name}\"\n")

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    assert rendered =~ "say"
    # Renders on one line (no raw list/control chars corrupting the message).
    assert length(String.split(rendered, "\n")) == 3
  end
end
