defmodule Cure.Elab.JoinGradeTest do
  @moduledoc """
  Slice 4c's join point vs slice 4b's usage check (adversarial review F11).

  The join point (4c) shares a `match`'s catch-all body across uncovered
  constructors by binding it once as `{:let, ω, S→R, {:lam, ω, S, body}, case}`. The
  usage check (4b) ω-scales every λ body's captured variables ("a closure may be
  entered any number of times"). So a `:linear`/`:affine` variable captured in the
  shared catch-all — used once regardless of which branch runs — was scaled to ω and
  REJECTED. A *sound* program rejected: an over-rejection, never unsound.

  Idris settles the design (`LinearCheck.idr:441-442`): it usage-checks each case
  alternative INDEPENDENTLY and combines by agreement; there is no shared capturing
  continuation at linearity-check time — sharing is a codegen concern. The join is a
  pure term-size optimization (for ESP32 flash), so the correct, sound-by-construction
  fix is to NOT apply it where it would be usage-checked with restricted grades: the
  usage check then sees the per-branch form, whose independent-branch agreement
  (`alt`) is already right. Grades are used nowhere in the stdlib, so this only
  affects future linear/affine code, and the join still fires for all ungraded code.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Validator}
  alias Cure.Elab.Program

  defp lets(env, name) do
    env |> Env.get_def(name) |> Map.fetch!(:body) |> Validator.nodes()
    |> Enum.count(&match?({:let, _, _, _, _}, &1))
  end

  defp calls(env, name, callee) do
    env |> Env.get_def(name) |> Map.fetch!(:body) |> Validator.nodes()
    |> Enum.count(&match?({:global, ^callee}, &1))
  end

  @enum "type C = A | B | D | E | G | H\n"

  describe "a restricted variable captured by a shared catch-all is not over-rejected" do
    test "a linear variable used once per branch through a catch-all is ACCEPTED" do
      src =
        "mod JG\n  #{@enum}" <>
          "  fn sink(x :linear Int) -> Int = x\n" <>
          "  fn f(x: C) -> Int =\n    let v :linear = 1\n    match x\n      A() -> sink(v)\n      _ -> sink(v)\nend\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "an affine variable captured by a catch-all is ACCEPTED" do
      src =
        "mod JG\n  #{@enum}" <>
          "  fn sink(x :linear Int) -> Int = x\n" <>
          "  fn f(x: C) -> Int =\n    let v :affine = 1\n    match x\n      A() -> sink(v)\n      _ -> sink(v)\nend\n"

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  describe "soundness is preserved — a genuinely over-used linear variable is still REJECTED" do
    test "a linear variable used TWICE in the catch-all body is rejected" do
      # `v` used twice in EVERY branch, so the over-use is unambiguous (not confounded
      # by an under-using sibling branch): agreement gives `:unrestricted`.
      src =
        "mod JG\n  #{@enum}" <>
          "  fn use2(a: Int, b: Int) -> Int = a\n" <>
          "  fn f(x: C) -> Int =\n    let v :linear = 1\n    match x\n      A() -> use2(v, v)\n      _ -> use2(v, v)\nend\n"

      assert {:error, {:usage_violation, %{declared: :linear, used: :unrestricted}}} =
               Program.elaborate(src)
    end

    test "a linear variable used in the catch-all AND after the match is rejected" do
      # `v` used inside the match and again in the enclosing expression → twice on the
      # path where the match returns and then `add` runs. Must reject.
      src =
        "mod JG\n  #{@enum}" <>
          "  fn sink(x :linear Int) -> Int = x\n" <>
          "  fn add(a: Int, b: Int) -> Int = a\n" <>
          "  fn f(x: C) -> Int =\n    let v :linear = 1\n" <>
          "    let r = match x\n      A() -> sink(v)\n      _ -> sink(v)\n    add(r, sink(v))\nend\n"

      assert {:error, {:usage_violation, %{declared: :linear}}} = Program.elaborate(src)
    end

    test "a linear variable used in ONLY SOME branches is rejected (must be used on every path)" do
      # A() does not use v; the catch-all does. On x = A(), v is never used → linear
      # violated. (This is the same answer the per-branch form gives via `alt`.)
      src =
        "mod JG\n  #{@enum}" <>
          "  fn sink(x :linear Int) -> Int = x\n" <>
          "  fn f(x: C) -> Int =\n    let v :linear = 1\n    match x\n      A() -> 0\n      _ -> sink(v)\nend\n"

      assert {:error, {:usage_violation, %{declared: :linear}}} = Program.elaborate(src)
    end
  end

  describe "the un-join's one-shot soundness gate" do
    # `relevance.ex`'s un-join fires on ANY `let`-bound λ over a `case`, not only the
    # compiler's join. A USER `let g = λ …` applied MORE THAN ONCE per path is NOT
    # one-shot, so its captures must NOT be counted once — the gate (`count_level ≤ 1`,
    # app-head only) falls back to the sound ω-scale. Here `g` captures linear `v` and
    # is applied twice in the `A()` branch, so `v` is used twice on that path → reject.
    # Weakening the gate would un-join this and accept it — UNSOUND.
    # A 2-constructor type with FULLY EXPLICIT branches (no `_`) so there is no
    # compiler catch-all join — only the user's `let g = λ …`, which is what the gate
    # governs.
    @two "type Two = T | F\n"

    test "a let-bound lambda applied twice per path, capturing a linear var, is REJECTED" do
      src =
        "mod JG\n  #{@two}" <>
          "  fn sink(x :linear Int) -> Int = x\n" <>
          "  fn add(a: Int, b: Int) -> Int = a\n" <>
          "  fn f(x: Two) -> Int =\n    let v :linear = 1\n" <>
          "    let g : (Int) -> Int = fn(k) -> sink(v)\n" <>
          "    match x\n      T() -> add(g(1), g(2))\n      F() -> add(g(1), g(2))\nend\n"

      assert {:error, {:usage_violation, %{used: :unrestricted}}} = Program.elaborate(src)
    end

    test "an AFFINE var captured by a lambda applied twice per path is REJECTED (gate soundness)" do
      # The sharp case: if the gate wrongly un-joined this, the twice-applied lambda's
      # non-tail applications would be walked as matched arms and the affine capture
      # LOST — read as 0 uses, which affine ACCEPTS. Loosening the gate (its non-bare
      # branch clause) flips this program from reject to accept — a verified
      # unsoundness. The tight gate rejects.
      src =
        "mod JG\n  #{@two}" <>
          "  fn asink(x :affine Int) -> Int = x\n" <>
          "  fn add(a: Int, b: Int) -> Int = a\n" <>
          "  fn f(x: Two) -> Int =\n    let v :affine = 1\n" <>
          "    let g : (Int) -> Int = fn(k) -> asink(v)\n" <>
          "    match x\n      T() -> add(g(1), g(2))\n      F() -> add(g(1), g(2))\nend\n"

      assert {:error, {:usage_violation, %{declared: :affine}}} = Program.elaborate(src)
    end
  end

  describe "the join optimization is preserved for ungraded code" do
    test "an ungraded 6-constructor catch-all still shares the body once (join fires)" do
      src =
        "mod JG\n  #{@enum}" <>
          "  fn kont(a: Int) -> Int = a\n" <>
          "  fn hit(a: Int) -> Int = a\n" <>
          "  fn f(x: C, n: Int) -> Int =\n    match x\n      A() -> hit(n)\n      _ -> kont(n)\nend\n"

      {:ok, env} = Program.elaborate(src)
      # Join fired: exactly one copy of the catch-all callee, bound by a `:let`.
      assert calls(env, :f, :kont) == 1
      assert lets(env, :f) == 1
    end
  end
end
