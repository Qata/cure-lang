defmodule Cure.Elab.MacroTypedRecordTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a computed rule exposes its derived record type to ordinary signatures" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <x: Code> computed by build_it

      fn helper(a: MkSyntax) -> Syntax =
        Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
