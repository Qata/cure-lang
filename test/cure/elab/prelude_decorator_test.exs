defmodule Cure.Elab.PreludeDecoratorTest do
  use ExUnit.Case, async: false

  @moduledoc """
  `@prelude` marks a stdlib item (or module) as implicitly in scope for every
  module — no `use` required. The canonical use is the `String` type alias:
  `@prelude typealias String = List(Char)` in `lib/std/string.cure` makes bare
  `String` resolve everywhere (List/Char are already ambient), so a signature can
  say `-> String` and a `"..."` literal checks against it.
  """

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
    :code.purge(mod)
  end

  test "String is ambient via @prelude — a bare String return type needs no use" do
    src = """
    mod PreludeStr
      fn greet() -> String = "hi"
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    # "hi" erases to the List(Char) cons spine [104, 105] (code points).
    assert mod.greet() == [?h, ?i]
  after
    purge(:"Cure.PreludeStr")
  end

  test "String is ambient inside a user ADT constructor field — no use" do
    src = """
    mod PreludeStrAdt
      type Result(T, E) = Ok(T) | Error(E)

      fn boom() -> Result(Int, String) = Error("bad")
    """

    assert {:ok, _mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
  after
    purge(:"Cure.PreludeStrAdt")
  end
end
