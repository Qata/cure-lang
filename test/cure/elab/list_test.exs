defmodule Cure.Elab.ListTest do
  @moduledoc """
  `List` value surface in the dependent pipeline (Wave 2). `[]`/`[h|t]`/`[a,b,c]`
  desugar to `Nil`/`Cons` ctor calls (reusing all ctor machinery) and emit as
  native BEAM cons cells. Tests use Int/Nat elements.

  Scope (revised mid-execution, spec §2 revision):
    * Nested list PATTERNS (`[a,b] ->`) are IN scope — the matrix compiler
      `desugar_nested_arms/2` lowers them before `constructor_pattern/1`.
    * A BARE top-level `[]` body (`fn e() -> List(Int) = []`) is infer-only-
      rejected (the `elaborate_body` third-dispatch-layer gap, Finding A) — the
      empty-list VALUE is proven in goal-bearing positions instead, and the bare
      body is pinned as a ledger guard.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  # SCOPE REVISION (mid-execution): a BARE top-level `[]` body is infer-only-
  # ambiguous (third-dispatch-layer / elaborate_body gap — Finding A, spec §2).
  # The empty-list VALUE is proven in a goal-bearing position instead; the bare
  # body is pinned as a ledger guard below. Do NOT touch the elaborate_body
  # whitelist to make the bare form pass (same discipline as Wave-1 pickup).
  test "an empty-list value elaborates in a goal-bearing position" do
    src = "mod M\n  fn single(h: Int) -> List(Int) = [h | []]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a bare top-level [] body is infer-only-rejected (ledger guard, NOT a crash)" do
    src = "mod M\n  fn e() -> List(Int) = []\nend\n"
    assert {:error, {:unsolved_metavariables, :Nil}} = Program.elaborate(src)
  end

  test "a multi-element list literal elaborates" do
    src = "mod M\n  fn xs() -> List(Int) = [1, 2, 3]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a cons literal elaborates" do
    src = "mod M\n  fn c(h: Int, t: List(Int)) -> List(Int) = [h | t]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a multi-head cons literal elaborates" do
    # Distinct parser path from both the plain [1,2,3] literal and the single
    # [h|t] cons above: `build_multi_head_cons/3` (parser.ex:837-843) desugars
    # [a, b | rest] right-associatively to [a | [b | rest]] BEFORE this node
    # ever reaches `:list` handling, so this exercises a genuinely different
    # AST shape than either other test (spec §3 antibody 3).
    src =
      "mod M\n  fn c(a: Int, b: Int, rest: List(Int)) -> List(Int) = [a, b | rest]\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a one-deep list pattern match elaborates" do
    src =
      @nat <>
        "  fn is_empty(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [] -> true\n" <>
        "      [h | t] -> false\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a mismatched-element list is rejected in checked position" do
    src = "mod M\n  fn bad() -> List(Int) = [1, true]\nend\n"
    assert {:error, _} = Program.elaborate(src)
  end

  # SCOPE REVISION (mid-execution): nested list patterns WORK on HEAD via the
  # matrix compiler `desugar_nested_arms/2` (elaborator.ex:2974), invoked by
  # elaborate_match/6 BEFORE constructor_pattern/1 could reject them. The
  # original plan wrongly expected `[a,b]` to be rejected via
  # nested_constructor_arg — that path never fires for list arms. This is now a
  # POSITIVE test (spec §2 revision + antibody 7). Runtime coverage is in Task 3.
  test "a nested list pattern elaborates" do
    src =
      @nat <>
        "  fn f(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [a, b] -> true\n" <>
        "      other -> false\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a list literal emits a NATIVE BEAM list" do
    src = "mod M\n  fn xs() -> List(Int) = [1, 2, 3]\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List1", functions: [:xs])

    result = apply(mod, :xs, [])
    assert result == [1, 2, 3]
    assert is_list(result)
  end

  # The empty-list VALUE (goal-bearing: a recursion whose base yields []). A bare
  # top-level `fn e() -> List(Int) = []` is infer-only-rejected (Finding A, spec
  # §2 / ledger guard above) — do NOT test that shape here.
  test "a recursion base yields the native empty list []" do
    src =
      "mod M\n" <>
        "  fn drop_all(xs: List(Int)) -> List(Int) =\n" <>
        "    match xs\n" <>
        "      [] -> xs\n" <>
        "      [h | t] -> drop_all(t)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List2", functions: [:drop_all])
    assert apply(mod, :drop_all, [[1, 2, 3]]) == []
    assert apply(mod, :drop_all, [[]]) == []
  end

  test "[h | t] builds the expected native list" do
    src = "mod M\n  fn c(h: Int, t: List(Int)) -> List(Int) = [h | t]\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List3", functions: [:c])
    assert apply(mod, :c, [1, [2, 3]]) == [1, 2, 3]
  end

  test "[a, b | rest] builds the expected native list (multi-head cons)" do
    # Cross-checks against the classic-pipeline oracle
    # test/cure/compiler/multi_head_cons_test.exs (Task 4 Step 3) — this is the
    # only directed test in this suite that exercises build_multi_head_cons/3.
    src =
      "mod M\n  fn c(a: Int, b: Int, rest: List(Int)) -> List(Int) = [a, b | rest]\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List3b", functions: [:c])
    assert apply(mod, :c, [1, 2, [3, 4]]) == [1, 2, 3, 4]
  end

  test "a one-deep list match selects the arm at runtime" do
    src =
      @nat <>
        "  fn is_empty(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [] -> true\n" <>
        "      [h | t] -> false\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List4", functions: [:is_empty])
    assert apply(mod, :is_empty, [[]]) == true
    assert apply(mod, :is_empty, [[:Z]]) == false
  end

  # SCOPE REVISION: nested list patterns work (matrix compiler). This proves
  # NATIVE emit preserves nested matching at runtime — the matrix compiler lowers
  # `[a, b]` to a chain of single-level `[H|T]` matches, each hitting
  # list_branch_clause, so native cons cells must select correctly at every level.
  test "a nested list pattern selects the arm at runtime (native emit)" do
    src =
      @nat <>
        "  fn exactly_two(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [a, b] -> true\n" <>
        "      other -> false\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List5", functions: [:exactly_two])
    assert apply(mod, :exactly_two, [[:Z, :Z]]) == true
    assert apply(mod, :exactly_two, [[:Z]]) == false
    assert apply(mod, :exactly_two, [[]]) == false
    assert apply(mod, :exactly_two, [[:Z, :Z, :Z]]) == false
  end
end
