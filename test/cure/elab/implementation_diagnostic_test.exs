defmodule Cure.Elab.ImplementationDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a mismatched method signature shows the required and provided types at the method" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool\n  implementation Eqs for Int\n    fn eqs(x: Int, y: Int) -> Int = 42\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "method_return.cure")

    assert {:method_signature_mismatch, %{interface: :Eqs, method: :eqs, expected: expected, actual: actual}} =
             Program.semantic_error(error)

    refute expected == actual

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATION METHOD HAS THE WRONG SIGNATURE [E105] ----- method_return.cure

             `eqs` in this `Eqs` implementation has a different signature from the method
             declared by the interface. Every parameter and the result must agree after
             substituting the implementation type.

             Expected: Int -> Int -> Bool
             Found:    Int -> Int -> Int

             at method_return.cure:5:5
             5 |     fn eqs(x: Int, y: Int) -> Int = 42
               |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this implementation provides the incompatible signature

             Hint: Change `eqs` to use the parameter and result types required by `Eqs`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 4, 38)
    assert lsp["relatedInformation"] == []

    assert lsp["data"]["payload"] == %{
             "actual_surface" => "Int -> Int -> Int",
             "expected_surface" => "Int -> Int -> Bool",
             "interface" => "Eqs",
             "kind" => "method_signature_mismatch",
             "method" => "eqs"
           }

    fixed = String.replace(source, "-> Int = 42", "-> Bool = true")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "method_return_fixed.cure")
  end

  test "a stray implementation method shows its full declaration and interface candidates" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool = true\n    fn nes(x: a, y: a) -> Bool = true\n  implementation Eqs for Int\n    fn eqz(x: Int, y: Int) -> Bool = int_eq(x, y)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "unknown_method.cure")

    assert {:unknown_interface_method, %{interface: :Eqs, method: :eqz, candidates: [:eqs, :nes]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- UNKNOWN MODULE MEMBER [E091] ---------------------------- unknown_method.cure

             `eqz` is not available in this member namespace.

             at unknown_method.cure:6:5
             6 |     fn eqz(x: Int, y: Int) -> Bool = int_eq(x, y)
               |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ `eqz` was not found

             Hint: Did you mean `eqs`, `nes`?
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(5, 4, 49)
    assert lsp["relatedInformation"] == []
    assert lsp["data"]["payload"]["candidates"] == ["eqs", "nes"]
    refute inspect(lsp["data"]["payload"]) =~ "source_info"
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
