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
      errors_of(
        "mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say goodbye\n"
      )

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
      errors_of(
        "mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say\n  fn g() = 1\n"
      )

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
end
