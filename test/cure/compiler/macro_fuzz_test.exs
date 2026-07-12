defmodule Cure.Compiler.MacroFuzzTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroFuzz
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program
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

  test "a well-typed expansion passes the generated proof batch" do
    source = """
    mod M
      macro Inc
        syntax inc <n: Nat> becomes n + 1
          example inc 0 expands 0 + 1
        explain
          Nat =>
            "expects a Nat"
          keyword "inc" =>
            "starts with inc"
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    {:macro_def, _, _} = macro_def = Enum.find(children, &match?({:macro_def, _, _}, &1))

    assert :ok = MacroFuzz.check_expansion_proof(macro_def, env, draws: 8, seed: 31)
  end

  test "an ill-typed generated expansion is reported by the proof batch" do
    source = """
    mod M
      macro Bad
        syntax bad <n: Nat> becomes n + true
          example bad 0 expands 0 + true
        explain
          Nat =>
            "expects a Nat"
          keyword "bad" =>
            "starts with bad"
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    {:macro_def, _, _} = macro_def = Enum.find(children, &match?({:macro_def, _, _}, &1))

    assert {:error, {:expansion_ill_typed, %{keyword: "bad"}}} =
             MacroFuzz.check_expansion_proof(macro_def, env, draws: 8, seed: 31)
  end
end
