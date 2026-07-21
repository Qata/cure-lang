defmodule Cure.Stdlib.RegexSourceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  test "the legacy regex engines and OTP runtime wrapper are absent" do
    legacy = Path.expand("../../../lib/cure/stdlib/cure_std_regex.ex", __DIR__)

    refute File.exists?(legacy)

    refute Enum.any?(Path.wildcard("lib/**/*.ex"), fn file ->
             File.read!(file) =~ ":re."
           end)

    regex_sources =
      Enum.filter(["lib/std/regex.cure"], &File.exists?/1) ++
        Path.wildcard("lib/std/regex/**/*.cure")

    refute Enum.any?(regex_sources, fn file ->
             source = File.read!(file)

             Enum.any?(
               ["type Regex =", "fn run_with", "fn repeat_all", "RawOptions", "ParseFailure"],
               &String.contains?(source, &1)
             )
           end)
  end

  test "slash literals retain the staged Std.Regex expansion entry" do
    {:ok, tokens} = Lexer.tokenize("fn f() = /[A-z]*/", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)

    assert {:function_def, _meta,
            [
              {:function_call, call_meta,
               [
                 {:literal, pattern_meta, "[A-z]*"},
                 {:literal, flags_meta, ""}
               ]}
            ]} = ast

    assert call_meta[:name] == "Std.Regex.literal"
    assert pattern_meta[:subtype] == :string
    assert flags_meta[:subtype] == :string
  end
end
