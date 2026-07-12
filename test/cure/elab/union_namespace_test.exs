defmodule Cure.Elab.UnionNamespaceTest do
  @moduledoc """
  The generated-family namespace must be RESERVED against user-declared names, and the
  union feature must not perturb programs that use no unions at all.

  Generated family keys are `Union<…>` / `Disjoint<…>` and their constructors are
  `<family>$<member_key>`, where a literal member keys as `<TypeKey>#<value>`. Every one of
  `< > | $ #` is a separator in that grammar — and every one is reachable in a
  BACKTICK-quoted identifier. A user name containing them can collide with, overwrite, or
  silently absorb a generated family or constructor.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src), do: Program.elaborate(src)

  defp dependent?(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Program.dependent?(ast)
  end

  describe "the union feature must not reroute a NON-union program to another pipeline" do
    test "an ADT constructor named `Equivalent` does not make a program dependent" do
      # `dependent?/1` decides WHICH COMPILER PIPELINE builds a module — and the two erase
      # constructors differently. Recursing it into a match arm's PATTERN (which lives in
      # meta, and was never visited before unions) exposed constructor patterns to the
      # pre-existing name-based "Equivalent"/"reflexive" heuristic, silently rerouting a
      # program that contains no `|` at all.
      src = """
      mod NR
        type Relation = Equivalent(Int, Int) | Different
        fn classify(r: Relation) -> Int = match r
          Equivalent(a, b) -> a
          Different -> 0
      end
      """

      refute dependent?(src)
    end

    test "a union in a match-arm pattern DOES still make a program dependent" do
      # The reason the :match_arm clause exists at all — do not regress it while fixing the
      # above.
      src = """
      mod DR
        fn f(x: Int | Bool) -> Int = match x
          n: Int -> n
          b: Bool -> 0
      end
      """

      assert dependent?(src)
    end
  end

  describe "the generated namespace is reserved against user-declared names" do
    test "an interface may not take a generated family name" do
      src = """
      mod I1
        interface `Union<Int|String>`(t)
          fn combine(a: t) -> Int
      end
      """

      assert {:error, {:reserved_union_type_name, _}} = elaborate(src)
    end

    test "a typealias may not take a generated family name" do
      src = """
      mod T1
        typealias `Union<Int|String>` = Bool
      end
      """

      assert {:error, {:reserved_union_type_name, _}} = elaborate(src)
    end

    test "a type name may not contain a key separator — it collides with a literal key" do
      # `Int#3` is EXACTLY the key `literal_key(:integer, 3)` produces. Unreserved, the two
      # members dedupe against each other and one is silently DROPPED from the union.
      src = """
      mod K1
        type `Int#3` = MkOnly
        fn f(x: `Int#3` | 3) -> Int = 1
      end
      """

      assert {:error, {:reserved_union_type_name, _}} = elaborate(src)
    end

    test "a constructor name may not contain a key separator" do
      src = """
      mod C1
        type Foo = `Union<Int|String>$Int`
      end
      """

      assert {:error, {:reserved_union_type_name, _}} = elaborate(src)
    end

    test "ordinary names are unaffected" do
      src = """
      mod OK
        type Colour = Red | Green
        typealias Alias = Int
        fn f(c: Colour) -> Int = match c
          Red() -> 1
          Green() -> 2
      end
      """

      assert {:ok, _} = elaborate(src)
    end
  end
end
