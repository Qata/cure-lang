# test/cure/compiler/macro_literal_test.exs
defmodule Cure.Compiler.MacroLiteralTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "a literal rule parses to a :literal-kind rule with a hole, a suffix, and a template" do
    node = parse!("macro Dur\n  literal <n: Number> ms becomes Duration.ms(n)\n")
    assert {:macro_def, _meta, [rule]} = node
    assert rule.kind == :literal
    assert rule.suffix == "ms"
    assert [{:hole, %{name: "n", kind: "Number"}}, {:lit, "ms"}] = rule.segments
    assert {:function_call, _, _} = rule.template
  end
end
