# Hardening tests for the @edition pragma placement/validation guard.
# Red-green coverage for audit findings F1 (decorator-led bypass), F3 (multiple
# pragmas), and F7 (malformed value silently accepted).
defmodule Cure.Compiler.EditionPragmaHardeningTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, file: "t.cure", emit_events: false)
    Parser.parse(toks, file: "t.cure", emit_events: false)
  end

  defp placement_error?(errors),
    do: Enum.any?(errors, &match?({:edition_pragma_placement, _, _}, &1))

  defp malformed_error?(errors),
    do: Enum.any?(errors, &match?({:edition_pragma_malformed, _, _}, &1))

  # F1 — a decorator-led definition (@extern/@derive/@builtin...) is substantive;
  # a later @edition is therefore misplaced and must be a hard error.
  test "F1: @edition after a @derive-led definition is a placement error" do
    src = "@derive(Show)\nrec R\n  x: Int\n@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert placement_error?(errors)
  end

  test "F1: @edition after an @extern-led fn is a placement error" do
    src =
      "@extern(:erlang, :length, 1)\nfn len(x: Int) -> Int\n@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"

    assert {:error, errors} = parse(src)
    assert placement_error?(errors)
  end

  # F3 — only the first @edition can be file-leading; a second is misplaced.
  test "F3: a second @edition pragma is a placement error" do
    src = "@edition(\"2026\")\n@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert placement_error?(errors)
  end

  # F7 — the pragma argument must be a 4-digit year string; anything else errors
  # rather than silently falling back to the default edition.
  test "F7: an unquoted-integer @edition value is a malformed-pragma error" do
    src = "@edition(2026)\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert malformed_error?(errors)
  end

  test "F7: a non-year string @edition value is a malformed-pragma error" do
    src = "@edition(\"abc\")\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert malformed_error?(errors)
  end

  test "F7: a bare @edition with no argument is a malformed-pragma error" do
    src = "@edition\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert malformed_error?(errors)
  end

  # Guard against over-correction: the happy path must still parse.
  test "a well-placed valid @edition still parses cleanly" do
    assert {:ok, _ast} = parse("@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n")
  end
end
