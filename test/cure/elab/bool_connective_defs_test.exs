defmodule Cure.Elab.BoolConnectiveDefsTest do
  @moduledoc """
  Phase 1 of retiring the Boolean-connective primitives: the connectives are now
  ordinary certified Cure functions over the inductive `Bool` in `Std.Bool`
  (`boolnot`/`booland`/`boolor`/`booleq`/`boolne`), each defined by
  `case`-elimination. This test certifies that the five defs load (total,
  well-typed) via the dependent elaborator/certifier and resolve as globals when
  `Std.Bool` is imported.

  The surface names `and`/`or`/`not` are Cure lexer keywords (operators), so they
  are NOT legal function identifiers; the defs use the `bool`-prefixed names,
  consistent with the spec's `booleq`/`boolne`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @connectives [:boolnot, :booland, :boolor, :booleq, :boolne]

  test "the five Std.Bool connective defs certify and resolve via import" do
    src =
      "mod M\n" <>
        "  use Std.Bool\n" <>
        "  fn c_not(a: Bool) -> Bool = boolnot(a)\n" <>
        "  fn c_and(a: Bool, b: Bool) -> Bool = booland(a, b)\n" <>
        "  fn c_or(a: Bool, b: Bool) -> Bool = boolor(a, b)\n" <>
        "  fn c_eq(a: Bool, b: Bool) -> Bool = booleq(a, b)\n" <>
        "  fn c_ne(a: Bool, b: Bool) -> Bool = boolne(a, b)\n" <>
        "end\n"

    assert {:ok, env} = Program.elaborate(src)

    for name <- @connectives do
      assert Map.has_key?(env.defs, name), "expected Std.Bool.#{name} to be a certified global"
    end
  end

  test "a connective applied to a non-Bool operand is rejected" do
    src =
      "mod M\n" <>
        "  use Std.Bool\n" <>
        "  fn bad() -> Bool = booland(1, true)\n" <>
        "end\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
