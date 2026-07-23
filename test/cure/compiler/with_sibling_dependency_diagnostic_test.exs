defmodule Cure.Compiler.WithSiblingDependencyDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  @source """
  mod DepSib
    type Req = A | B
    type Cap1(r: Req) indices ()
      MkC1 : Cap1(r)
    type Cap2(r: Req, c1: Cap1(r)) indices ()
      MkC2 : Cap2(r, c1)
    type Done = D
    fn handle(r: Req, c1: Cap1(r), c2: Cap2(r, c1)) -> Done = with r
      A() -> D
      B() -> D
  end
  """

  test "a refined sibling depending on another refined sibling labels both parameter types and the with" do
    {diagnostic, registry, error} = diagnostic(@source)

    assert {:with_sibling_dependency_unsupported, :sibling_references_sibling} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH CANNOT REFINE DEPENDENT SIBLINGS IN THIS ORDER [E093] ----- dep_sib.cure

             `c2` must be refined when this `with` chooses a constructor, but its type also
             depends on `c1`, which must be refined by the same match. Cure cannot currently
             generalize one refined sibling over another without changing their dependency
             order.

             at dep_sib.cure:8:36
              8 |   fn handle(r: Req, c1: Cap1(r), c2: Cap2(r, c1)) -> Done = with r
                >                       ---------    ^^^^^^^^^^^^^            ------ `c1` must also be refined by this match; the type of `c2` depends on another value refined by this `with`
                >                                                                  - this is the value whose constructor would refine those sibling types
              9 |     A() -> D
                > ------------
             10 |     B() -> D
                > ------------ this `with` requires the unsupported dependent refinement

             Hint: Nest a second match after refining `c1`, or change `c2` so its type does not depend on `c1`
             """)

    assert diagnostic.payload == %{
             kind: :with_sibling_dependency_unsupported,
             reason: :sibling_references_sibling,
             checking: :handle,
             dependent: "c2",
             dependency: "c1"
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(7, 35, 7, 48)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(7, 22, 7, 31),
             range(7, 65, 7, 66),
             range(7, 60, 9, 12)
           ]

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]
  end

  test "removing the cross-sibling dependency compiles" do
    repaired =
      @source
      |> String.replace("type Cap2(r: Req, c1: Cap1(r))", "type Cap2(r: Req)")
      |> String.replace("Cap2(r, c1)", "Cap2(r)")

    assert {:ok, _env} = Program.elaborate(repaired, file: "dep_sib.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "dep_sib.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "dep_sib.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
