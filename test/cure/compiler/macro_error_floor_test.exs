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
end
