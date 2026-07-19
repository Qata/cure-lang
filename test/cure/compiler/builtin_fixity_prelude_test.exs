defmodule Cure.Compiler.BuiltinFixityPreludeTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.Parser.{BuiltinFixity, FixityTable}

  test "operators.cure carries @prelude" do
    {:ok, src} = File.read("lib/std/operators.cure")
    assert src =~ ~r/@prelude\s*\n\s*mod Std\.Operators/
  end

  test "the built-in table still declares the core operators" do
    t = BuiltinFixity.table()
    for op <- ["+", "*", "|>", "==", "✉", "<-|", "."] do
      assert FixityTable.declares?(t, op), "expected built-in table to declare #{op}"
    end
  end

  test "the built-in table is memoized (same term on repeat)" do
    assert BuiltinFixity.table() == BuiltinFixity.table()
  end
end
