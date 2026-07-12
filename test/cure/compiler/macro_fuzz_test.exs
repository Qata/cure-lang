defmodule Cure.Compiler.MacroFuzzTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroFuzz
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Context, Eval, Kernel}

  test "samples well-typed Core fillers for supported grammar categories" do
    for category <- ["Nat", "Bd", "Vec"] do
      assert {:ok, %{ctx: ctx, goal: goal}, terms} = MacroFuzz.sample_holes(category, 12, 19)
      goal_value = Eval.eval(goal, Context.env(ctx))

      assert length(terms) == 12
      assert Enum.all?(terms, &(Kernel.check(ctx, &1, goal_value) == :ok))
    end
  end

  test "unsupported grammar categories are reported as coverage gaps" do
    assert {:error, {:unsupported_hole_type, "Code"}} = MacroFuzz.hole_generator("Code")
  end

  test "generated scalar fillers assemble into fully consumed macro uses" do
    source = """
    macro Inc
      syntax inc <n: Nat> becomes n + 1
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, rules}} = Parser.parse(tokens, emit_events: false)
    rule = Enum.find(rules, &(&1[:kind] == :syntax))
    assert {:ok, _info, terms} = MacroFuzz.sample_holes("Nat", 8, 29)

    for term <- terms do
      assert {:ok, use_site} = MacroFuzz.assemble_use_site(rule, %{"n" => term})
      expansion = Parser.expand_example(rules, use_site)
      refute match?({:example_use_site_not_fully_consumed, _, _}, expansion)
      assert {:binary_op, _, _} = expansion
    end
  end

  test "a filler with no supported surface encoding is reported" do
    source = "macro M\n  syntax m <x: Nat> becomes x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)

    assert {:error, {:unsupported_surface_filler, _}} =
             MacroFuzz.assemble_use_site(rule, %{"x" => {:global, :missing_surface}})
  end
end
