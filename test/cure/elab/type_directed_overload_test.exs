defmodule Cure.Elab.TypeDirectedOverloadTest do
  use ExUnit.Case, async: false

  @moduletag :overload

  # TARGET PIN — type-directed overload resolution (spec
  # `docs/superpowers/specs/2026-07-10-overloading-and-argument-labels-design.md`,
  # design approved `b25081ee`, build deferred). Several functions share a name
  # and the CALL SITE picks the right one from the surrounding type context
  # (Idris2 "elaborate-and-prune", keyed by `(name, arity, argument types)`).
  #
  # This unblocks the stdlib rename workarounds: `Std.Measurements` exposes
  # `add`/`sub` only because a bare `plus` collides with ambient `Std.Nat.plus`;
  # `Std.Char.code_point` is a rename to dodge `Std.String.to_int`. With a
  # type-directed resolver both keep their natural name and the argument type
  # decides. See [[overloading-and-argument-labels-spec]],
  # [[std-units-literal-of-measure-landed]].
  #
  # SCOPE — NAMED resolution only. Making the `+` OPERATOR "just work" on a user
  # type is deliberately OUT of scope here: operator conformance is deferred
  # until a Swift-style precedence-group + custom-infix syntax structure is
  # spec'd, so `+` is resolved as a declared operator (associativity/precedence)
  # rather than hard-coded as a third special case in `elaborate_expr_typed`
  # (alongside the existing Semigroup and Ord routing). That test arrives with
  # the precedence-group spec, not this pin.
  #
  # TODAY (genuinely red — verified against the tree): an overload SET is
  # rejected outright — two `fn plus` in scope fail with
  # `{:codegen_error, {:duplicate_definition, :plus}}`. The surface cannot even
  # EXPRESS a set: globals resolve by bare name, so a duplicate is a collision,
  # not a candidate list. GREEN REQUIRES the front-end to gather an overload set
  # under one name, then prune by argument type at the call site (spec §4). When
  # implemented, delete the `@tag :skip` and this must pass.
  @tag :skip
  test "a bare overloaded name resolves by argument type at the call site" do
    src = """
    mod TypeDirectedOverloadName
      type Meters = MkM(Int)
      type Grams = MkG(Int)

      fn plus(a: Meters, b: Meters) -> Meters = match a
        MkM(x) -> match b
          MkM(y) -> MkM(x + y)

      fn plus(a: Grams, b: Grams) -> Grams = match a
        MkG(x) -> match b
          MkG(y) -> MkG(x + y)

      fn add_m() -> Int = match plus(MkM(3), MkM(4))
        MkM(x) -> x

      fn add_g() -> Int = match plus(MkG(10), MkG(20))
        MkG(x) -> x
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.TypeDirectedOverloadName"

    assert apply(mod, :add_m, []) == 7
    assert apply(mod, :add_g, []) == 30
  end

  # Task 3 — registration probe. Two type-distinct `plus` members must both
  # register under discriminated keys (no silent overwrite, no
  # duplicate_definition). No overloaded CALL appears here: pruning an applied
  # overloaded call arrives with Task 5; this test asserts only that the surface
  # can now EXPRESS the set.
  test "two same-name defs both register (no silent overwrite)" do
    src = """
    mod OverloadReg
      type Meters = MkM(Int)
      type Grams = MkG(Int)
      fn plus(a: Meters, b: Meters) -> Meters = a
      fn plus(a: Grams, b: Grams) -> Grams = a
    end
    """

    assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
  end
end
