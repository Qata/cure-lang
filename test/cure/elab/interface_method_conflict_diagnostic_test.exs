defmodule Cure.Elab.InterfaceMethodConflictDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a shared interface method labels both authored declarations" do
    source =
      "mod M\n  interface Eqs(a)\n    fn size(x: a) -> Int\n  interface Ord(a)\n    fn size(x: a) -> Bool\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "method_conflict.cure")

    assert {:ambiguous_method, :size, [:Eqs, :Ord]} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- METHOD `SIZE` IS DECLARED BY MULTIPLE INTERFACES [E089] -- method_conflict.cure

             Both `Eqs` and `Ord` declare `size`. Interface methods share one unqualified
             namespace, so Cure could not determine which declaration an unqualified
             `size(...)` call should use.

             at method_conflict.cure:5:8
             3 |     fn size(x: a) -> Int
               |        ---- `size` is also declared by `Eqs` here
             4 |   interface Ord(a)
             5 |     fn size(x: a) -> Bool
               |        ^^^^ `Ord` repeats the interface method `size`

             Hint: Rename `size` in one interface so every interface method has a unique name
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 7, 11)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(2, 7, 11)
    assert related["message"] == "`size` is also declared by `Eqs` here"

    assert lsp["data"]["payload"] == %{
             "declarations" => [%{"interface" => "Eqs"}, %{"interface" => "Ord"}],
             "interfaces" => ["Eqs", "Ord"],
             "kind" => "ambiguous_method",
             "method" => "size"
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    fixed = String.replace(source, "fn size(x: a) -> Bool", "fn rank(x: a) -> Bool")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "method_conflict_fixed.cure")
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
