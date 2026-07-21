defmodule Cure.Stdlib.RegexSourceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  @regex_source Path.expand("../../../lib/std/regex.cure", __DIR__)

  test "the Regex standard library is a pure Cure implementation" do
    source = File.read!(@regex_source)

    refute source =~ "@extern"
    refute source =~ "cure_std_regex"

    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
  end

  test "the legacy OTP regex runtime wrapper is absent" do
    legacy = Path.expand("../../../lib/cure/stdlib/cure_std_regex.ex", __DIR__)

    refute File.exists?(legacy)

    refute Enum.any?(Path.wildcard("lib/**/*.ex"), fn file ->
             File.read!(file) =~ ":re."
           end)
  end

  test "slash literals expand to the typed pure Regex constructor" do
    {:ok, tokens} = Lexer.tokenize("fn f() -> Regex = /[A-z]*/", emit_events: false)
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
