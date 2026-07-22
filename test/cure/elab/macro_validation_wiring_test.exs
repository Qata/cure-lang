defmodule Cure.Elab.MacroValidationWiringTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "compilation rejects a macro with an uncovered diagnosis point" do
    source = """
    mod M
      macro Every
        syntax every <t: Duration> becomes t
        explain
          keyword "every" =>
            "starts with every"
    """

    assert {:error, {:source_context, {:missing_diagnosis, points}, %{span: %Cure.Diagnostic.Span{}}}} =
             Program.elaborate(source)

    assert {:hole_kind, "Duration"} in points
  end

  test "compilation rejects an unpinned syntax rule" do
    source = """
    mod M
      macro Now
        syntax now becomes 0
        explain
          keyword "now" =>
            "starts with now"
    """

    assert {:error, {:source_context, {:rule_unpinned, ["now"]}, %{span: %Cure.Diagnostic.Span{}}}} =
             Program.elaborate(source)
  end

  test "compilation points at a computed hole that claims the reserved context field" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <context: Code> contextual computed by build_it

      fn build_it(input: MkSyntax) -> Syntax = input.context
    """

    assert {:error,
            {:source_context, {:reserved_syntax_field, "context", ["mk"]},
             %{
               span: %Cure.Diagnostic.Span{start_line: 5, start_column: 15},
               rule_spans: [%Cure.Diagnostic.Span{}]
             }} = reason} = Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "reserved_context.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO HOLE USES A RESERVED NAME [E092] ---------------- reserved_context.cure

             The hole `context` in the `mk` rule conflicts with the reflected expansion
             context supplied to computed rules.

             at reserved_context.cure:5:15
             5 |     syntax mk <context: Code> contextual computed by build_it
               |               ^^^^^^^^^^^^^^^ this hole name is reserved for expansion context

             Hint: Rename this hole; `context` is supplied automatically
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 4, "character" => 14},
             "end" => %{"line" => 4, "character" => 29}
           }
  end

  test "compilation rejects a mismatched syntax expansion pin" do
    source = """
    mod M
      macro Now
        syntax now becomes 0
          example now expands 1
        explain
          keyword "now" =>
            "starts with now"
    """

    assert {:error,
            {:source_context, {:example_mismatch, [%{keyword: "now", source_span: %Cure.Diagnostic.Span{}}]},
             %{span: %Cure.Diagnostic.Span{}, rule_spans: [%Cure.Diagnostic.Span{}]}} = reason} =
             Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "example_pin.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXAMPLE HAS THE WRONG EXPANSION [E092] --------------- example_pin.cure

             Macro example(s) do not match their actual expansions: now.

             at example_pin.cure:4:7
             3 |     syntax now becomes 0
               |     -------------------- this rule owns the failing example
             4 |       example now expands 1
               |       ^^^^^^^^^^^^^^^^^^^^^ this pin does not match the actual expansion

             Hint: Update the pinned expansion or fix the macro rule
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 3, "character" => 6},
             "end" => %{"line" => 3, "character" => 27}
           }
  end

  test "compilation accepts a fully pinned computed rule" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <x: Code> computed by build_it
          example mk 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "mk" =>
            "starts with mk"

      fn build_it(a: MkSyntax) -> Syntax = a.x
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "compilation accepts a type-only syntax example pin" do
    source = """
    mod M
      macro One
        syntax one becomes 1
          example one expands : Int
        explain
          keyword "one" =>
            "starts with one"
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "compilation rejects a type-only syntax example pin with the wrong type" do
    source = """
    mod M
      macro One
        syntax one becomes 1
          example one expands : String
        explain
          keyword "one" =>
            "starts with one"
    """

    assert {:error,
            {:source_context, {:example_type_mismatch, [%{keyword: "one", source_span: %Cure.Diagnostic.Span{}}]},
             %{span: %Cure.Diagnostic.Span{}, rule_spans: [%Cure.Diagnostic.Span{}]}} = reason} =
             Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "example_type.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXAMPLE HAS THE WRONG TYPE [E092] ------------------- example_type.cure

             Macro example(s) have the wrong type: one.

             at example_type.cure:4:7
             3 |     syntax one becomes 1
               |     -------------------- this rule owns the failing example
             4 |       example one expands : String
               |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this pinned type does not accept the expansion

             Hint: Use the expansion's actual type or fix the macro rule
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 3, "character" => 6},
             "end" => %{"line" => 3, "character" => 34}
           }
  end

  test "compilation rejects a macro whose generated expansion is ill-typed" do
    source = """
    mod M
      macro Bad
        syntax bad <n: Code> becomes n + true
          example bad 0 expands 0 + true
        explain
          Code =>
            "expects code"
          keyword "bad" =>
            "starts with bad"
    """

    assert {:error, {:expansion_ill_typed, %{keyword: "bad", shrunk_term: _}}} =
             Program.elaborate(source)
  end
end
