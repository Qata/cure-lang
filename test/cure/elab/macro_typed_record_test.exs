defmodule Cure.Elab.MacroTypedRecordTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a computed rule exposes its derived record type to ordinary signatures" do
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

      fn helper(a: MkSyntax) -> Syntax =
        Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))

      fn build_it(a: MkSyntax) -> Syntax = a.x
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a computed rule passes its typed record to the elab and reflects a projected field" do
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
      fn f(n: Int) -> Int = mk n
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a computed rule rejects a projection of an undeclared syntax field" do
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

      fn build_it(a: MkSyntax) -> Syntax = a.missing
    """

    assert {:error, error} = Program.elaborate(source)
    assert {:unknown_field, :"M#MkSyntax", "missing", [:x, :context]} = Program.semantic_error(error)
  end

  test "a computed elab can guard its continuation with check and fail" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        fail BadInput(input: Code)
        syntax mk <x: Code> computed by build_it
          example mk 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "mk" =>
            "starts with mk"
          BadInput =>
            "input is not valid"

      fn build_it(a: MkSyntax) -> Syntax =
        check true else fail BadInput(a.x)
        a.x

      fn f(n: Int) -> Int = mk n
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a false computed guard reports the declared author failure" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        fail BadInput(input: Code)
        syntax mk <x: Code> computed by build_it
          example mk 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "mk" =>
            "starts with mk"
          BadInput =>
            "input is not valid"

      fn build_it(a: MkSyntax) -> Syntax =
        check false else fail BadInput(a.x)
        a.x

      fn f(n: Int) -> Int = mk n
    """

    assert {:error, {:computed_macro_error, _meta, {:author_failure, "BadInput", [_]}} = reason} =
             Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "author_failure.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- COMPUTED MACRO EXPANSION FAILED [E092] ------------------ author_failure.cure

             The `mk` computed macro could not produce valid Cure syntax: macro rejected
             expansion: the macro reported `BadInput`

             at author_failure.cure:20:25
             20 |   fn f(n: Int) -> Int = mk n
                |                         ^^^^ this macro invocation generated the failing syntax

             Note: Edit the authored macro invocation or its rule; generated syntax is not
                   the user-facing source.

             Hint: Fix the `BadInput` condition reported by this macro

             expansion: mk
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 19, "character" => 24},
             "end" => %{"line" => 19, "character" => 28}
           }
  end
end
