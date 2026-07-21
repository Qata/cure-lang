defmodule Cure.Elab.TotalityWiringTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @types """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  """

  @gadt """
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  test "a total type-level function is certified; the whole program elaborates" do
    src = @types <> "fn andd(x: Dec, y: Dec) -> Dec = x\n" <> @gadt
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a non-total function used in a type is rejected (totality required)" do
    # andd is self-recursive (non-total) yet appears in SF's computed index,
    # so it is type-level and MUST be total — §6 negative #3.
    src = @types <> "fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)\n" <> @gadt
    assert {:error, error} = Program.elaborate(src, file: "totality.cure")
    assert {:totality_required, :"Main#andd"} = Program.semantic_error(error)

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "totality.cure", src)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.code == "E013"
    assert diagnostic.primary.span.start_line == 4
    assert diagnostic.primary.span.start_column == 4
    assert diagnostic.primary.message == "this definition is used in a type and must always terminate"
    assert rendered =~ "-- FUNCTION MUST BE TOTAL [E013]"
    assert rendered =~ "4 | fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)"
    assert rendered =~ "   ^^^^ this definition is used in a type and must always terminate"
    assert rendered =~ "Hint: Make each recursive call use a structurally smaller argument"
    assert rendered =~ "Runtime-only functions may remain partial"

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 3},
             "end" => %{"line" => 3, "character" => 7}
           }
  end

  test "a non-total function used only at runtime is NOT required to be total" do
    # loop is self-recursive but referenced in no type ⇒ stays partial, allowed.
    src =
      @types <>
        "fn andd(x: Dec, y: Dec) -> Dec = x\n" <>
        @gadt <>
        "fn loop(x: Dec) -> Dec = loop(x)\n"

    assert {:ok, _env} = Program.elaborate(src)
  end
end
