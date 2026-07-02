defmodule Cure.Elab.RecordTest do
  @moduledoc """
  Records (Idris parity), declaration + construction. A record `rec Point\n  x: T
  \n  y: U` is elaborated as a single-constructor family whose constructor shares
  the family name and whose argument telescope is *named by the fields* — the
  field names live on the constructor telescope, so no separate registry is needed
  and the kernel treats the names as plain labels.

  Because the constructor and the family share a name, `resolve_index_name` (which
  runs only in type positions) resolves the shared name to the *family*, so
  `p: Point` / `-> Point` are types while `Point(..)` / `Point{..}` are values.

  Record construction `Point{x: .., y: ..}` desugars to the positional constructor
  `Point(.., ..)`, ordering the field values by the constructor telescope, so field
  order is free and a missing/extra field is rejected. Fields are read back by
  pattern matching (`match p | Point(a, b) -> a`); the `p.x` projection sugar is a
  separate step. Oracle `record/rc01_construct_match` pins accept/accept.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @pt "mod M\n  type Nat = Z | S(Nat)\n  rec Point\n    x: Nat\n    y: Nat\n"

  test "a record constructs positionally and is read by pattern matching" do
    src =
      @pt <>
        "  fn getx(p: Point) -> Nat = match p\n    Point(a, b) -> a\n" <>
        "  fn g() -> Nat = getx(Point(S(Z()), Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecPos", functions: [:getx, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "brace construction with fields in declaration order" do
    src =
      @pt <>
        "  fn getx(p: Point) -> Nat = match p\n    Point(a, b) -> a\n" <>
        "  fn g() -> Nat = getx(Point{x: S(Z()), y: Z()})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecBrace", functions: [:getx, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "brace construction is order-independent" do
    src =
      @pt <>
        "  fn gety(p: Point) -> Nat = match p\n    Point(a, b) -> b\n" <>
        "  fn g() -> Nat = gety(Point{y: S(Z()), x: Z()})\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.RecReorder", functions: [:gety, :g])

    # y = S(Z) even though it was written first.
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a missing record field is rejected" do
    assert {:error, {:record_field_mismatch, :Point}} =
             Program.elaborate(@pt <> "  fn g() -> Point = Point{x: S(Z())}\nend\n")
  end

  test "an unknown record field is rejected" do
    assert {:error, {:record_field_mismatch, :Point}} =
             Program.elaborate(@pt <> "  fn g() -> Point = Point{x: S(Z()), z: Z()}\nend\n")
  end
end
