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

  test "a computed rule passes its typed record to the elab and reflects a projected field" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <x: Code> computed by build_it

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

      fn build_it(a: MkSyntax) -> Syntax = a.missing
    """

    assert {:error, {:unknown_field, :MkSyntax, "missing"}} = Program.elaborate(source)
  end
end
