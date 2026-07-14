defmodule Cure.Compiler.PrinterPrecedenceTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}

  # The printer used to drop grouping parentheses unconditionally, so a
  # sub-expression whose precedence is LOWER than its surrounding operator was
  # reprinted without the parens the parser needs to recover it — silently
  # changing the program's meaning on every `cure fmt` / `cure migrate`. E.g.
  # `(x + 1) * 2` was reprinted as `x + 1 * 2`, which reparses as `x + (1 * 2)`.
  #
  # These tests pin the fix: parse -> print -> parse must recover a structurally
  # identical AST (parentheses may be added/removed, but never in a way that
  # changes the parse). We compare meta-stripped trees so that only shape and
  # operators — not line/col — are asserted.

  defp strip(node) do
    case node do
      {tag, _meta, kids} when is_list(kids) -> {tag, Enum.map(kids, &strip/1)}
      {tag, _meta, kid} -> {tag, strip(kid)}
      list when is_list(list) -> Enum.map(list, &strip/1)
      other -> other
    end
  end

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    ast
  end

  # Each entry is the RHS expression of a `fn` body.
  @exprs [
    "(x + 1) * 2",
    "x * (x + 1)",
    "1 - (2 - x)",
    "(x - 1) - 2",
    "(if x > 0 then 1 else 2) + 1",
    "1 + (if x > 0 then 1 else 2)",
    "a or (b and c)",
    "(a or b) and c",
    "-(x + 1)",
    "not (a and b)",
    "(a <> b) <> c",
    "a <> (b <> c)",
    # Non-`:binary_op` infix nodes the parser lowers specially — range (`..`),
    # send (`<-|`), and dot access (`.`) — must also parenthesise their operands
    # (as parents) and be parenthesised (as operands) by precedence.
    "(1..2) + 3",
    "3 + (1..2)",
    "(a == b)..c",
    "(pid <-| msg) + 1",
    "(a + b).x",
    "a.b + c",
    "Std.Map.put(k, v, m)",
    # `|>` lowers to a pipe-tagged :function_call (not :binary_op) and binds
    # loosest (level 10); the right-extending prefix keywords (`throw`, `yield`,
    # …) grab everything to their right. Both must be parenthesised as operands.
    "(a |> f) + b",
    "b + (a |> f)",
    "(a |> f) < b",
    "(a |> f).x",
    "a |> f |> g",
    "(a <-| b) |> f",
    "(throw x) + 1",
    "(yield x) + 1"
  ]

  for expr <- @exprs do
    @expr expr
    test "precedence-preserving reprint: #{expr}" do
      src =
        "mod M\n  fn f(x: Int, a: Int, b: Int, c: Int, pid: Int, msg: Int, k: Int, v: Int, m: Int) -> Int = #{@expr}\n"

      ast = parse!(src)
      out = Printer.quoted_to_string(ast)
      reparsed = parse!(out)

      assert strip(ast) == strip(reparsed),
             "reprint changed the parse.\n  in:  #{@expr}\n  out: #{out}"
    end
  end
end
