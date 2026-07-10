defmodule Cure.Compiler.ParserGrammarStrictnessTest do
  @moduledoc """
  Two ways the parser accepted syntax the spec forbids.

  **A keyword slot that checked only the token type.** `expect(state, expected_type)`
  compares `token.type` and never `token.value`, so `expect(state, :keyword)` in a slot
  documented — by the comment directly above it — as consuming one specific keyword
  swallowed *any* keyword. `impl Show when Int` parsed as `impl Show for Int`. No error
  was recorded, and since the keyword's value never reaches the AST, no later stage could
  notice the substitution either. `expect_keyword/2`, which checks both, already existed
  and was already used elsewhere. Three sites now use it: `impl … for`,
  `implementation … for`, and a supervisor child's `Module as child_id`.

  **Non-associativity that was never implemented.** The spec's operator table and
  `Precedence`'s moduledoc both say comparison, range, and the Melquiades send are
  non-associative and that the parser rejects chaining. It didn't. `right_bp = left_bp + 1`
  is exactly what a *left*-associative operator uses: it stops the operator from swallowing
  a peer on its own right-hand side, and does nothing to stop the Pratt loop from picking
  the freshly-built node back up as a new left operand at the caller's `min_bp`. So
  `a == b == c` left-chained, and `a <-| b <-| c` nested into two sends — the first send's
  return value re-sent to `c`, the exact fan-out `Precedence`'s moduledoc says
  non-associativity exists to prevent. Rejection now lives in the loop, where the token
  after the operator is visible.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse_raw(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    Parser.parse(tokens, emit_events: false)
  end

  defp parse!(source) do
    assert {:ok, ast} = parse_raw(source)
    ast
  end

  describe "a keyword slot accepts only its own keyword" do
    test "`impl Proto for Type` rejects another keyword in place of `for`" do
      assert {:error, _} = parse_raw("impl Show when Int\n  fn show(x: Int) -> String = \"x\"\n")
    end

    test "`implementation Iface for Type` rejects another keyword in place of `for`" do
      assert {:error, _} =
               parse_raw("implementation Show when Int\n  fn show(x: Int) -> String = \"x\"\n")
    end

    test "a supervisor child spec rejects another keyword in place of `as`" do
      assert {:error, _} = parse_raw("sup App.Root\n  children\n    Counter when counter\n")
    end

    test "the correct keyword still parses" do
      assert {:ok, _} = parse_raw("impl Show for Int\n  fn show(x: Int) -> String = \"x\"\n")
      assert {:ok, _} = parse_raw("sup App.Root\n  children\n    Counter as counter\n")
    end
  end

  describe "non-associative operators reject chaining" do
    test "comparison: `a == b == c`" do
      assert {:error, errors} = parse_raw("a == b == c")
      assert Enum.any?(errors, &match?({:non_associative, :==, :chained_with, :==, _, _}, &1))
    end

    test "comparison, mixed operators at the same level: `a < b <= c`" do
      assert {:error, errors} = parse_raw("a < b <= c")
      assert Enum.any?(errors, &match?({:non_associative, :<, :chained_with, :<=, _, _}, &1))
    end

    test "range: `a..b..c`" do
      assert {:error, errors} = parse_raw("a..b..c")
      assert Enum.any?(errors, &match?({:non_associative, :.., :chained_with, :.., _, _}, &1))
    end

    test "Melquiades send: `a <-| b <-| c`" do
      assert {:error, errors} = parse_raw("a <-| b <-| c")
      assert Enum.any?(errors, &match?({:non_associative, :"<-|", :chained_with, :"<-|", _, _}, &1))
    end
  end

  describe "associative operators still chain" do
    test "`a + b + c` left-associates" do
      assert {:binary_op, _, [{:binary_op, _, [_a, _b]}, _c]} = parse!("a + b + c")
    end

    test "`a + b == c + d` groups the comparison outermost" do
      assert {:binary_op, meta, [{:binary_op, _, _}, {:binary_op, _, _}]} = parse!("a + b == c + d")
      assert Keyword.get(meta, :operator) == :==
    end

    test "a single comparison of two arithmetic chains is not a chain" do
      assert {:ok, _} = parse_raw("a * b < c * d")
    end

    test "comparisons joined by `and` are not a chain" do
      assert {:ok, _} = parse_raw("a < b and b < c")
    end
  end
end
