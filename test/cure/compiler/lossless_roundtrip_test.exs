defmodule Cure.Compiler.LosslessRoundtripTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}

  # Local helper (test modules do not share `defp` helpers across files --
  # this is NOT the same function as `PrinterTotalityTest`'s `parse!/2`,
  # it is a separate copy for this module).
  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  defp comments(src) do
    src
    |> String.split("\n")
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/#+\s?(.*)$/, line) do
        [_, txt] -> [String.trim(txt)]
        _ -> []
      end
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.sort()
  end

  @corpus Path.wildcard("lib/std/*.cure")

  for file <- @corpus do
    # NB: `@file` is a reserved Elixir attribute (it sets the stacktrace file
    # for the next def and reads back as nil), so the loop value is captured
    # under `@f` instead. This is the only deviation from the plan's verbatim
    # text and it changes no assertion.
    @f file
    test "lossless round-trip preserves every comment: #{file}" do
      src = File.read!(@f)
      {:ok, toks, trivia} = Lexer.tokenize(src, file: @f, trivia: true)
      {:ok, ast} = Parser.parse(toks, file: @f, emit_events: false)
      out = ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()

      # every comment present in the source is present in the output
      assert comments(src) -- comments(out) == []
      # and the output reparses
      assert _ = parse!(out, @f)
    end
  end

  # §5.4 point 5 (multi-line *expression* span, e.g. a blank inside a multi-line
  # map/list/record literal) is VACUOUS for Cure: the language has no multi-line
  # collection-literal syntax at all -- a `%{`, `[`, or `(` that spans a newline
  # fails to reparse (`expected :rbrace/:rbracket, got :dedent`). Verified
  # 2026-07-10 against Parser.parse/2. There is therefore no in-language source
  # that can exercise point 5, and the plan's original `blank_in_map` test
  # encoded a feature Cure does not have (it failed at the *parse* step, before
  # any printing). It is replaced below by tests of the rules that DO apply to
  # Cure -- the statement-list rules 1, 3, and 4. See spec §5.4 point 5.

  test "§5.4 rules 1 & 3: 0 blank lines at top of file; exactly 1 between every top-level definition" do
    # No blank between a/b; a 3-blank run between b/c; two leading blanks at top.
    src = "\n\nmod M\nfn a() -> Int = 1\nfn b() -> Int = 2\n\n\n\nfn c() -> Int = 3\n"

    {:ok, toks, trivia} = Lexer.tokenize(src, file: "top.cure", trivia: true)
    {:ok, ast} = Parser.parse(toks, file: "top.cure", emit_events: false)
    out = ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()

    assert out == "mod M\n\nfn a() -> Int = 1\n\nfn b() -> Int = 2\n\nfn c() -> Int = 3"
    assert _ = parse!(out, "top.cure")
  end

  test "§5.4 rule 4: inside a block body, a single author blank between statements is preserved (and a run caps at 1)" do
    # One blank between `let x` and `let y`; a 3-blank run between `let y` and
    # `z` must collapse to a single blank; the trailing blank is trimmed.
    src = "mod M\nfn f() -> Int =\n  let x = 1\n\n  let y = 2\n\n\n\n  let z = 3\n  z\n"

    {:ok, toks, trivia} = Lexer.tokenize(src, file: "body.cure", trivia: true)
    {:ok, ast} = Parser.parse(toks, file: "body.cure", emit_events: false)
    out = ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()

    assert out =~ ~r/let x = 1\n[ ]*\n[ ]*let y = 2/, "single author blank not preserved: #{inspect(out)}"
    assert out =~ ~r/let y = 2\n[ ]*\n[ ]*let z = 3/, "blank run not capped to 1: #{inspect(out)}"
    # no double blank anywhere (run capped)
    refute out =~ ~r/\n[ ]*\n[ ]*\n/, "an uncapped multi-blank run survived: #{inspect(out)}"
    assert _ = parse!(out, "body.cure")
  end
end
