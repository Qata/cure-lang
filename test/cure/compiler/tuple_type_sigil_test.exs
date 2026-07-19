defmodule Cure.Compiler.TupleTypeSigilTest do
  @moduledoc """
  Tuple TYPES may be written with the `%[A, B]` sigil, mirroring the value tuple `%[a, b]` and removing the
  long-standing inconsistency where values were `%[a, b]` but their types were `(A, B)`. `%[A, B]` produces the
  same `{:tuple_type, …}` node as `Tuple(A, B)` (including optional per-position binders for a dependent
  telescope), so resolution, display, and codegen are unchanged; `(A, B)` still parses (now soft-deprecated).

  Original `%[A, B]` proposal: Aleksei Matiushkin (am-kantox); re-implemented here against the dependent parser.
  """
  use ExUnit.Case, async: true

  test "%[A, B] is a tuple type, identical to Tuple(A, B) in value and projection" do
    src = """
    mod M
      fn sig() -> %[Int, Bool] = %[1, true]
      fn named() -> Tuple(Int, Bool) = %[1, true]
      fn proj(p: %[Int, Bool]) -> Int = p.1
      fn three() -> %[Int, Int, Int] = %[1, 2, 3]
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    # %[A, B] and Tuple(A, B) produce the identical flat BEAM tuple.
    assert apply(mod, :sig, []) == {1, true}
    assert apply(mod, :sig, []) == apply(mod, :named, [])
    assert apply(mod, :proj, [{7, true}]) == 7
    assert apply(mod, :three, []) == {1, 2, 3}
  end

  test "%[A, B] accepts per-position binders like Tuple(x: A, B) — a dependent telescope" do
    # The binder syntax `x: T` is retained (same node as `Tuple(x: A, B)`); here the binder is unused, but the
    # form is what lets a later position depend on an earlier one.
    src = """
    mod D
      fn f(p: %[x: Int, Bool]) -> Int = p.1
      fn g(p: Tuple(x: Int, Bool)) -> Int = p.1
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :f, [{5, true}]) == 5
    assert apply(mod, :f, [{5, true}]) == apply(mod, :g, [{5, true}])
  end

  test "the legacy parenthesised tuple type (A, B) still parses (my change didn't break it)" do
    # `(A, B)` as a tuple type parses to the legacy `{:tuple, [], …}` node (soft-deprecated toward `%[A, B]`).
    # It is parse-level backward compat only — on the dependent pipeline the legacy node does not codegen (which
    # is precisely why `%[A, B]`/`Tuple(A, B)` are the working forms and `(A, B)` is deprecated).
    src = "mod L\n  fn legacy(p: (Int, Bool)) -> Int = 0\n"
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
  end
end
