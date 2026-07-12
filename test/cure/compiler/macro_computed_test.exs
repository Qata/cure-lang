# test/cure/compiler/macro_computed_test.exs
defmodule Cure.Compiler.MacroComputedTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp rules({:macro_def, _, rs}), do: rs
  defp rules({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &rules/1)
  defp rules(_), do: nil

  test "a `computed by` rule parses to a :computed rule capturing the elab reference" do
    [rule] = rules(parse!("macro Mk\n  syntax mk <x: Code> computed by build_it\n"))
    assert rule.kind == :computed
    assert rule.keyword == "mk"
    assert [{:hole, %{name: "x", kind: "Code"}}] = rule.segments
    assert {:variable, _, "build_it"} = rule.elab
  end

  test "a `becomes` rule still parses to a :syntax rule (non-breaking)" do
    [rule] = rules(parse!("macro Now\n  syntax now becomes Clock.now()\n"))
    assert rule.kind == :syntax
    assert {:function_call, _, _} = rule.template
  end

  test "a :computed rule is NOT dispatched at a use-site yet (inert until execution slice)" do
    node = parse!("mod M\n  macro Mk\n    syntax mk computed by build_it\n  fn f() = mk\n")

    find = fn find, n ->
      case n do
        {:function_def, meta, [body]} -> if(to_string(Keyword.get(meta, :name)) == "f", do: body)
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    assert {:variable, _, "mk"} = find.(find, node)
  end
end
