defmodule Cure.Std.OperatorBootstrapTest do
  @moduledoc """
  Phase-3 bootstrap gate: the operator-defining stdlib modules must parse
  WITHOUT relying, in a body, on an infix/prefix operator they themselves define.

  These five modules are what *populates* the compiler's built-in operator table:
  `operators.cure` declares every precedence group + operator fixity, and the
  interface modules (`equatable`/`comparable`/`arithmetic`/`bool`) supply the
  backing methods. If any of them used, in a body, an infix operator it itself
  defines, the parser could not bootstrap — it would need the very table these
  modules produce before they finish parsing. The discipline that keeps this
  acyclic is that they call their operators only in **backtick prefix-call form**
  (`` `==`(a, b) ``), via `Std.Builtin.<op>` / `Std.Bool.<op>`, or via
  `match`/`pickup` — never as an infix or prefix operator expression.

  ## What "against an empty fixity table" means here, honestly

  `Cure.Compiler.Parser.parse/2` always seeds its Pratt binding-power table from
  the memoized built-in table (`BuiltinFixity.table()`); there is no `opts`
  switch to hand it a custom/empty table. The compiler DOES have one genuine
  empty-table seam — the `:cure_building_fixity_table` process flag, which makes
  `session_builtin_fixity_table/0` return `FixityTable.new()` — but it is only
  clean for `operators.cure`, whose body is entirely inert declarations. For the
  interface modules that flag is *too* aggressive: it also strips the
  non-overloadable **builtin** operators `operators.cure` declares (notably the
  `.` module/field projection those modules use in `Std.Builtin.int_eq(...)`),
  which none of these modules *defines*. Under it, `Std.Builtin.int_eq` silently
  mis-parses (`Std` as a variable, `.Builtin`/`.int_eq(...)` as stray forced
  patterns) yet still returns `{:ok, _}` — a false pass. So an `{:ok, _}`
  assertion under that flag would not actually verify anything for four of the
  five modules.

  In real compilation the ordering is: `operators.cure` is parsed FIRST against
  an empty table (this very seam, in `BuiltinFixity.compute/0`) to build the
  table; the four interface modules are then parsed against the FULL built-in
  table. So the only module with a hard empty-table obligation is
  `operators.cure`, and it is exercised genuinely below. The property that
  matters for the other four — "no body uses an operator it itself defines" — is
  verified structurally: parse them through the real default pipeline and assert
  their AST contains ZERO infix/prefix operator nodes (`:binary_op`/`:unary_op`).
  Every operator use survives as a `:function_call` (backtick form) or a
  `Std.Builtin.*` call, never as an operator node, which is exactly the acyclic
  discipline the bootstrap requires.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}

  @operator_defining_modules ~w(operators.cure equatable.cure comparable.cure arithmetic.cure bool.cure)

  defp std_source(file), do: File.read!(Path.join([File.cwd!(), "lib", "std", file]))

  defp parse_default(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    Parser.parse(tokens, file: file, emit_events: false)
  end

  # Count `:binary_op` / `:unary_op` nodes anywhere in a MetaAST tree. A
  # hand-rolled walk (MetaAST nodes are not standard Elixir AST).
  defp operator_nodes(node) when is_tuple(node) do
    here =
      case node do
        {tag, _meta, _} when tag in [:binary_op, :unary_op] -> [node]
        _ -> []
      end

    here ++ (node |> Tuple.to_list() |> Enum.flat_map(&operator_nodes/1))
  end

  defp operator_nodes(list) when is_list(list), do: Enum.flat_map(list, &operator_nodes/1)
  defp operator_nodes(_other), do: []

  test "operators.cure parses against a genuinely empty fixity table" do
    # The load-bearing bootstrap obligation: `operators.cure` is parsed to BUILD
    # the built-in table, so it must parse with NO table present. This is exactly
    # `BuiltinFixity.compute/0`'s seam. It is all inert precedence/fixity
    # declarations, so an empty table parses it faithfully (no false-pass risk).
    prev = Process.put(:cure_building_fixity_table, true)

    try do
      assert {:ok, _ast} = parse_default(std_source("operators.cure"), "operators.cure"),
             "operators.cure must parse against an empty fixity table — it is the source " <>
               "the built-in table is bootstrapped from"
    after
      case prev do
        nil -> Process.delete(:cure_building_fixity_table)
        _ -> Process.put(:cure_building_fixity_table, prev)
      end
    end
  end

  test "operator-defining stdlib modules use no infix/prefix operator in any body" do
    for f <- @operator_defining_modules do
      assert {:ok, ast} = parse_default(std_source(f), f), "#{f} must parse"

      nodes = operator_nodes(ast)

      assert nodes == [],
             "#{f} uses an infix/prefix operator in a body (found #{length(nodes)} operator " <>
               "node(s): #{inspect(nodes, limit: 5)}). An operator-defining bootstrap module " <>
               "must call its operators only in backtick prefix-call form (`` `==`(a, b) ``), " <>
               "via `Std.Builtin.<op>`/`Std.Bool.<op>`, or via `match`/`pickup` — never as an " <>
               "operator expression that would need the very fixity table it helps define."
    end
  end
end
