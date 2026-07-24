defmodule Cure.Stdlib.DependentRegexAbsoluteBoundaryTest do
  use ExUnit.Case, async: false

  setup_all do
    source = """
    mod RegexAbsoluteBoundaryRuntime
      use Std.Regex
      fn absolute_start_search(input: String) -> Option(Match(Unit)) = search(/\\Aabc/m, input)
      fn strict_end_search(input: String) -> Option(Match(Unit)) = search(/abc\\z/, input)
      fn final_end_search(input: String) -> Option(Match(Unit)) = search(/abc\\Z/, input)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "\\A, \\z, and \\Z retain absolute subject semantics", %{runtime_module: module} do
    assert apply(module, :absolute_start_search, [~c"x\nabc"]) == :none
    assert apply(module, :strict_end_search, [~c"abc\n"]) == :none

    assert apply(module, :final_end_search, [~c"abc\n"]) ==
             {:some, {:Match, :unit, ~c"", ~c"abc", ~c"\n"}}
  end
end
