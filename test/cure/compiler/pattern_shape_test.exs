defmodule Cure.Compiler.PatternShapeTest do
  @moduledoc """
  The classic pattern compiler used to answer four unrecognized pattern shapes with the
  same thing: `{:var, line, :_}`, an unconditional wildcard.

    * a bare `None` (no parens). `docs/MATCH.md` §5.12 forbids it and E074 was written up
      for it, but `grep -rn E074 lib/` found only the catalog entry — no stage ever raised
      it. `do_compile/2` sent every `{:variable, _, name}` to `compile_variable_pattern/2`
      with no case check, so `None` bound a variable that matched everything. Expression
      position had the check (`Codegen.compile_variable/2` special-cases exactly this
      shape); pattern position didn't.
    * an as-pattern, `whole @ Some(x)`. No clause at all — both the binding and the inner
      pattern were dropped.
    * a range, `1..10`. The clause existed, and its comment promised "the type checker will
      flag it". Nothing did.
    * a call whose head isn't capitalized, `some(x)` — a typo for `Some(x)`. Match arms are
      parsed by the general expression parser, so it reaches pattern position as an
      ordinary `{:function_call, …}` and fell through `compile_call_pattern/3`'s `true ->`.

  Each swallowed every scrutinee and shadowed every arm below it: a silent miscompilation
  with no diagnostic. Maranget's algorithm specializes over a *closed* set of head shapes,
  and Idris 2 and Lean both make an input outside that set a hard error; a wildcard row is
  only ever introduced deliberately, by an actual `_` or variable in the source. The
  compiler now raises `PatternCompiler.Error`, which `Codegen.compile_module/2` returns as
  `{:error, {:pattern_error, code, message, line}}`.

  The as-pattern is the one shape that is legal and was simply unimplemented here; it now
  compiles to Erlang's `Whole = {some, X}`. The dependent elaborator has understood it all
  along, and `test/oracle/match/verdicts.json` pins its runtime semantics.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{BeamWriter, Codegen, Lexer, Parser, PatternCompiler}

  defp compile(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Codegen.compile_module(ast, emit_events: false)
  end

  defp compile_module!(source) do
    assert {:ok, forms, _warnings} = compile(source)
    {:ok, module} = BeamWriter.compile_and_load(forms)
    module
  end

  @opt "  type Opt = Some(Int) | None\n"

  describe "rejected shapes" do
    test "a bare nullary constructor in pattern position is E074" do
      source = """
      mod BareNullary
      #{@opt}
        fn describe(o: Opt) -> Int =
          match o
            None -> 0
            Some(x) -> x
      """

      assert {:error, {:pattern_error, "E074", message, _line}} = compile(source)
      assert message =~ "write `None()`"
    end

    test "a range pattern is rejected, not compiled to a wildcard" do
      source = """
      mod RangePattern
        fn classify(x: Int) -> Int =
          match x
            1..10 -> 1
            _ -> 0
      """

      assert {:error, {:pattern_error, "E090", message, _line}} = compile(source)
      assert message =~ "range patterns are not supported"
    end

    test "a lowercase call head is rejected, not compiled to a wildcard" do
      # `some(x)` — neither a record nor a constructor. It used to bind everything and
      # discard the argument `x` entirely.
      ast = {:function_call, [name: "some", line: 1], [{:variable, [], "x"}]}

      assert_raise PatternCompiler.Error, ~r/`some\(…\)` is not a constructor/, fn ->
        PatternCompiler.compile(ast, %Codegen{})
      end
    end

    test "an unrecognized pattern node is rejected rather than silently wildcarded" do
      # Through `apply/3`: `compile/2`'s argument type is now narrow enough that a direct
      # call with an unhandled node is a compile-time type warning, which is the point.
      assert_raise PatternCompiler.Error, ~r/unrecognized pattern shape/, fn ->
        apply(PatternCompiler, :compile, [{:lambda, [line: 1], []}, %Codegen{}])
      end
    end
  end

  describe "as-patterns" do
    test "`whole @ Some(x)` matches only Some-shaped values" do
      source = """
      mod AsPattern
      #{@opt}
        fn mk_none() -> Opt = None()
        fn mk_some(x: Int) -> Opt = Some(x)

        fn classify(o: Opt) -> Int =
          match o
            whole @ Some(x) -> 1
            None() -> 0
      """

      module = compile_module!(source)

      assert module.classify(module.mk_some(5)) == 1
      assert module.classify(module.mk_none()) == 0
    end

    test "the as-binding names the whole scrutinee, not the inner sub-pattern" do
      source = """
      mod AsPatternBinds
      #{@opt}
        fn mk_some(x: Int) -> Opt = Some(x)

        fn whole_of(o: Opt) -> Opt =
          match o
            whole @ Some(x) -> whole
            None() -> None()
      """

      module = compile_module!(source)
      some_5 = module.mk_some(5)

      assert module.whole_of(some_5) == some_5
    end
  end

  describe "shapes that still compile" do
    test "an explicit nullary constructor `None()` is fine" do
      source = """
      mod ExplicitNullary
      #{@opt}
        fn mk_none() -> Opt = None()

        fn describe(o: Opt) -> Int =
          match o
            None() -> 0
            Some(x) -> x
      """

      module = compile_module!(source)
      assert module.describe(module.mk_none()) == 0
    end

    test "a lowercase variable, a wildcard, and a negative literal are all patterns" do
      source = """
      mod StillPatterns
        fn classify(x: Int) -> Int =
          match x
            -1 -> 0
            n -> n
      """

      module = compile_module!(source)

      assert module.classify(-1) == 0
      assert module.classify(7) == 7
    end
  end
end
