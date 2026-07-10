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

  test "a blank line inside a multi-line map literal is preserved verbatim (§5.4 point 5, not a statement list)" do
    src = """
    mod M
    fn f() -> Int =
      let m = %{
        x: 1,

        y: 2
      }
      1
    """

    {:ok, toks, trivia} = Lexer.tokenize(src, file: "blank_in_map.cure", trivia: true)
    {:ok, ast} = Parser.parse(toks, file: "blank_in_map.cure", emit_events: false)
    out = ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()

    # the blank line between the two map entries survives the reprint --
    # points 1-4's statement-list normalization does not apply inside a map
    # literal (there is no enclosing block/statement-list here), so nothing
    # should collapse or inject it.
    assert out =~ ~r/x:\s*1,\s*\n\s*\n\s*y:\s*2/
    assert _ = parse!(out, "blank_in_map.cure")
  end
end
