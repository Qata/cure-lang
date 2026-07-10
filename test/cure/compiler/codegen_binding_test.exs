defmodule Cure.Compiler.CodegenBindingTest do
  @moduledoc """
  Erlang variables are single-assignment. The classic codegen forgot that in three places,
  and forgot to catch its own `throw` in a fourth.

    * `compile_variable/2` resolved a name straight through `mangle_var/1` and never
      consulted `state.vars`. `compile_assignment/4` lowered a shadowing `let` through
      `PatternCompiler.compile_variable_pattern/2`'s already-bound branch — which exists
      for NON-LINEAR PATTERNS (`[x, x]`, where the second `x` must equal the first), mints
      a fresh variable plus an equality guard, and deliberately leaves `state.vars[name]`
      on the ORIGINAL atom. `compile_assignment/4` then threw the guard away. So
      `let x = 1; let x = 2; x` bound a fresh unused Erlang variable and evaluated to 1.

    * the counter that keeps two dups in one pattern apart, `pattern_dup_counter`, was
      declared on the codegen struct and read by `fresh_var_atom/2` but incremented
      nowhere. Every dup in a clause collapsed onto `V__dup_x_0`, so a third `let` shadow
      re-matched a variable already bound to the second shadow's value: `{badmatch, _}`.

    * `x += 1` emitted Erlang's `V_x = V_x + 1`. `V_x` is bound, so that is a re-match, not
      a rebinding: it demands `old == old + 1`. Every augmented assignment on a bound
      variable crashed.

    * `return e` throws `{:cure_return, e}` so it can unwind out of an `if` arm.
      `grep -rn cure_return lib/` found exactly one hit — the throw. No catch existed
      anywhere in the pipeline, so a `return` outside a user-written `try` escaped the
      function and blew up its caller.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{BeamWriter, Codegen, Lexer, Parser}

  defp eval!(source, fun \\ :main, args \\ []) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, forms, _warnings} = Codegen.compile_module(ast, emit_events: false)
    {:ok, module} = BeamWriter.compile_and_load(forms)
    apply(module, fun, args)
  end

  describe "let shadowing" do
    test "a shadowed binding is what later references see" do
      assert eval!("""
             mod ShadowOnce
               fn main() -> Int =
                 let x = 1
                 let x = 2
                 x
             """) == 2
    end

    test "a third shadow of the same name does not crash" do
      assert eval!("""
             mod ShadowThrice
               fn main() -> Int =
                 let x = 1
                 let x = 2
                 let x = 3
                 x
             """) == 3
    end

    test "a shadow reads the previous binding on its right-hand side" do
      assert eval!("""
             mod ShadowReadsPrevious
               fn main() -> Int =
                 let x = 1
                 let x = x + 10
                 let x = x + 100
                 x
             """) == 111
    end

    test "shadowing a function parameter works" do
      assert eval!(
               """
               mod ShadowParam
                 fn twice(n: Int) -> Int =
                   let n = n * 2
                   n
               """,
               :twice,
               [21]
             ) == 42
    end

    test "a let inside one branch does not leak its rebinding to the sibling branch" do
      source = """
      mod BranchScope
        fn pick(b: Bool, x: Int) -> Int =
          pickup
            b ->
              let x = 99
              x
            else -> x
      """

      assert eval!(source, :pick, [true, 7]) == 99
      assert eval!(source, :pick, [false, 7]) == 7
    end
  end

  describe "augmented assignment" do
    test "`x += 1` increments the binding" do
      assert eval!("""
             mod AugAdd
               fn main() -> Int =
                 let x = 1
                 x += 1
                 x
             """) == 2
    end

    test "repeated augmented assignments accumulate" do
      assert eval!("""
             mod AugRepeat
               fn main() -> Int =
                 let x = 1
                 x += 2
                 x *= 10
                 x -= 5
                 x
             """) == 25
    end

    test "`/=` on floats divides rather than raising badarith" do
      assert eval!("""
             mod AugFloatDiv
               fn main() -> Float =
                 let x = 3.0
                 x /= 2.0
                 x
             """) == 1.5
    end
  end

  describe "early return" do
    test "`return` returns from the enclosing function instead of escaping it" do
      source = """
      mod EarlyReturn
        fn classify(x: Int) -> Int = if x > 0 then return 1 else 0
      """

      assert eval!(source, :classify, [5]) == 1
      assert eval!(source, :classify, [-5]) == 0
    end

    test "a function with no `return` is not wrapped" do
      assert eval!("""
             mod NoReturn
               fn main() -> Int = 41 + 1
             """) == 42
    end
  end

  describe "non-linear patterns" do
    test "three occurrences of one name in a pattern each get a distinct Erlang variable" do
      source = """
      mod TripleDup
        fn all_same(t: Tuple) -> Bool =
          match t
            %[x, x, x] -> true
            _ -> false
      """

      assert eval!(source, :all_same, [{1, 1, 1}]) == true
      assert eval!(source, :all_same, [{1, 1, 2}]) == false
      assert eval!(source, :all_same, [{1, 2, 1}]) == false
    end
  end
end
