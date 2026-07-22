defmodule Cure.Elab.MacroRecursiveExpansionTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.MacroExpand
  alias Cure.Elab.Program

  test "nested computed macros normalize inside out before the outer macro runs" do
    source = """
    mod M
      use Std.Syntax

      macro Inner
        syntax inner <x: Code> computed by build_inner
          example inner 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "inner" =>
            "starts with inner"

      macro Outer
        syntax outer <x: Code> computed by build_outer
          example outer 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "outer" =>
            "starts with outer"

      fn build_inner(input: InnerSyntax) -> Syntax = input.x
      fn build_outer(input: OuterSyntax) -> Syntax = input.x
      fn f(n: Int) -> Int = outer inner n
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "the recursive reducer enforces an explicit AST budget" do
    assert {:ok, env} = Program.elaborate("mod M\n  fn f() -> Int = 0\n")

    assert {:error, {:macro_expansion_budget, :node_count, []}} =
             MacroExpand.expand({:literal, [subtype: :integer], 0}, env, max_nodes: 0)
  end

  test "computed expansion diagnostics retain the invocation provenance" do
    assert {:ok, env} = Program.elaborate("mod M\n  fn f() -> Int = 0\n")

    node =
      {:computed_use, [keyword: "inner", line: 17, col: 5],
       [{:variable, [scope: :local], "missing_builder"}, {:macro_input, [], []}]}

    assert {:error, {:computed_macro_error, meta, _reason}} =
             MacroExpand.expand(node, env,
               callback_context: %{behaviour: :gen_server, callback: :handle_info, arity: 2}
             )

    assert [%{keyword: "inner", line: 17, col: 5}] = meta[:provenance]
    assert meta[:expansion_context] == %{behaviour: :gen_server, callback: :handle_info, arity: 2}
  end

  test "an expansion budget reports the complete active invocation chain" do
    assert {:ok, env} = Program.elaborate("mod M\n  fn f() -> Int = 0\n")

    node =
      {:computed_use, [keyword: "outer", line: 21, col: 2],
       [{:variable, [scope: :local], "missing_builder"}, {:macro_input, [], []}]}

    assert {:error, {:macro_expansion_budget, :expansion_count, [%{keyword: "outer", line: 21, col: 2}]}} =
             MacroExpand.expand(node, env, max_expansions: 0)
  end

  test "a real parsed expansion budget points at the invocation and preserves provenance" do
    source = """
    mod M
      macro Loop
        syntax loop <x: Code> contextual computed by build_loop
      fn build_loop(input: LoopSyntax) -> Syntax = input.x
      fn run() -> Int = loop 0
    """

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro_budget.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "macro_budget.cure", emit_events: false)
    assert {:computed_use, _, _} = invocation = find_computed_use(ast)

    assert {:error,
            {:macro_expansion_budget, :expansion_count,
             [%{keyword: "loop", invocation: %Cure.Diagnostic.Span{start_line: 5, start_column: 21}}]}} =
             reason =
             MacroExpand.expand(invocation, Env.empty(), max_expansions: 0)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "macro_budget.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXPANSION LIMIT EXCEEDED [E092] --------------------- macro_budget.cure

             Macro expansion exceeded its expansion_count limit.

             at macro_budget.cure:5:21
             5 |   fn run() -> Int = loop 0
               |                     ^^^^^^ the expansion limit is reached here

             Hint: Reduce the generated expansion depth or split this macro into smaller steps

             expansion: loop
             """)

    assert [%Cure.Diagnostic.ProvenanceFrame{invocation: %Cure.Diagnostic.Span{start_line: 5}}] =
             diagnostic.provenance

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 4, "character" => 20},
             "end" => %{"line" => 4, "character" => 26}
           }
  end

  test "quoted syntax is not recursively expanded" do
    assert {:ok, env} = Program.elaborate("mod M\n  fn f() -> Int = 0\n")

    quoted = {:quoted_syntax, [], [{:computed_use, [keyword: "inner"], []}]}
    assert {:ok, ^quoted} = MacroExpand.expand(quoted, env)
    refute MacroExpand.contains_computed_use?(quoted)
  end

  defp find_computed_use({:computed_use, _meta, _children} = node), do: node

  defp find_computed_use({_tag, _meta, children}) when is_list(children),
    do: Enum.find_value(children, &find_computed_use/1)

  defp find_computed_use(list) when is_list(list), do: Enum.find_value(list, &find_computed_use/1)
  defp find_computed_use(_other), do: nil
end
