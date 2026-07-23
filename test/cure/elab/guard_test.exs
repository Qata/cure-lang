defmodule Cure.Elab.GuardTest do
  @moduledoc """
  Boolean `when` guards on a variable/catch-all pattern desugar to a chain of
  `bool_elim`: `match n | x when g -> a | x -> b` becomes `bool_elim g a b`,
  with each guard test its own Boolean elimination and the final unguarded
  catch-all closing the chain (the fall-through when every guard is false).

  Guards need surface comparison operators to elaborate, so `{:binary_op}`
  lowers to a builtin-op global spine (K2, spec 2026-07-09; e.g. `x == 0` ->
  `int_eq x 0`). Both build on the committed `bool_elim`; no kernel change.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a surface comparison operator elaborates and runs on the BEAM" do
    src =
      "mod M\n" <>
        "  fn eq0(n: Int) -> Bool = n == 0\n" <>
        "  fn t() -> Bool = eq0(0)\n  fn f() -> Bool = eq0(7)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard0", functions: [:eq0, :t, :f])

    assert apply(mod, :t, []) == true
    assert apply(mod, :f, []) == false
  end

  test "a single guard with a catch-all fallback runs on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x -> S(Z())\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard1", functions: [:classify, :a, :b])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
  end

  test "a chain of guards falls through to the correct arm on the BEAM" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x when x == 1 -> S(Z())\n" <>
        "    x -> S(S(Z()))\n" <>
        "  fn a() -> Nat = classify(0)\n" <>
        "  fn b() -> Nat = classify(1)\n" <>
        "  fn c() -> Nat = classify(9)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Guard2", functions: [:classify, :a, :b, :c])

    assert apply(mod, :a, []) == :Z
    assert apply(mod, :b, []) == {:S, :Z}
    assert apply(mod, :c, []) == {:S, {:S, :Z}}
  end

  test "multi-parameter function clauses bind tuple leaves in guards and bodies" do
    src = """
    mod M
      fn choose(char: Char, fallback: Char) -> Char
        | char, fallback when char == '.' -> char
        | _, fallback -> fallback

      fn hit() -> Char = choose('.', 'x')
      fn miss() -> Char = choose('a', 'x')
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.GuardMulti", functions: [:choose, :hit, :miss])

    assert apply(mod, :hit, []) == ?.
    assert apply(mod, :miss, []) == ?x
  end

  test "a guard whose test is false and has no fallback is rejected (non-exhaustive)" do
    src =
      @nat <>
        "  fn classify(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x when x == 1 -> S(Z())\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "a fallback binder shadowed inside its branch labels both bindings" do
    src =
      @nat <>
        "  fn f(n: Int) -> Nat = match n\n" <>
        "    x when x == 0 -> Z()\n" <>
        "    x ->\n" <>
        "      let g : (Int) -> Nat = fn(x) -> Z()\n" <>
        "      g(x)\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:unsupported_guard,
              %{reason: :shadowed, name: "x", site: :body, span: outer_span, shadow_span: shadow_span}}, _} =
              error} = Program.elaborate(src)

    assert {outer_span.start_line, outer_span.start_column} == {5, 5}
    assert {shadow_span.start_line, shadow_span.start_column} == {6, 33}

    {diagnostic, registry} = Errors.to_diagnostic(error, "guard_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FALLBACK BRANCH SHADOWS `X` [E090] ------------------------ guard_shadow.cure

             This fallback branch substitutes the matched value for `x`, but a binder inside
             the branch uses the same name. That substitution could capture the inner value.

             at guard_shadow.cure:6:33
             5 |     x ->
               |     - this guard pattern binds `x`
             6 |       let g : (Int) -> Nat = fn(x) -> Z()
               |                                 ^ rename this inner binder so it does not shadow `x`

             Hint: Give the nested binder a different name and update its branch expression
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 32},
             "end" => %{"line" => 5, "character" => 33}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 4, "character" => 4},
             "end" => %{"line" => 4, "character" => 5}
           }

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_guard",
             "name" => "x",
             "reason" => "shadowed",
             "site" => "body"
           }

    fixed = String.replace(src, "fn(x) -> Z()", "fn(value) -> Z()")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "guard_shadow_fixed.cure")
  end

  test "a refutable literal guard points at the pattern and condition" do
    src =
      @nat <>
        "  fn f(n: Int) -> Nat = match n\n" <>
        "    0 when true -> Z()\n" <>
        "    _ -> S(Z())\n" <>
        "end\n"

    assert {:error,
            {:source_context, {:unsupported_guard, %{reason: :refutable_pattern, shape: :literal, span: pattern_span}},
             _} = error} =
             Program.elaborate(src)

    assert {pattern_span.start_line, pattern_span.start_column} == {4, 5}

    {diagnostic, registry} = Errors.to_diagnostic(error, "literal_guard.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LITERAL PATTERN CANNOT CARRY THIS GUARD [E093] ----------- literal_guard.cure

             This literal pattern can fail before its `when` condition is considered. The
             current guard chain only accepts variable, wildcard, or irrefutable tuple
             patterns.

             at literal_guard.cure:4:5
             4 |     0 when true -> Z()
               |     ^      ---- this refutable pattern cannot enter the guard chain; this condition is attached to the refutable pattern

             Hint: Match this pattern first, then test the condition inside its branch and keep an explicit fallback
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 4},
             "end" => %{"line" => 3, "character" => 5}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 3, "character" => 11},
             "end" => %{"line" => 3, "character" => 15}
           }

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_guard",
             "reason" => "refutable_pattern",
             "shape" => "literal"
           }

    fixed = String.replace(src, "    0 when true -> Z()\n", "    0 -> Z()\n")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "literal_guard_fixed.cure")
  end

  test "a guarded non-variable scrutinee with a named fallback is evaluated once" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match S(n)\n" <>
        "    S(x) when true -> x\n" <>
        "    other -> other\n" <>
        "end\n"

    {:ok, environment} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(environment, module: :"Cure.GuardStableScrutinee", functions: [:f])

    assert apply(mod, :f, [:Z]) == :Z
    assert apply(mod, :f, [{:S, :Z}]) == {:S, :Z}
  end

  test "guard lowering preserves the duplicate catch-all diagnostic" do
    src =
      @nat <>
        "  fn f(n: Nat) -> Nat = match n\n" <>
        "    S(x) when true -> x\n" <>
        "    a -> a\n" <>
        "    b -> b\n" <>
        "end\n"

    assert {:error, {:source_context, {:duplicate_default_pattern, "b"}, _} = error} =
             Program.elaborate(src)

    {diagnostic, registry} = Errors.to_diagnostic(error, "guard_defaults.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PATTERN MATCH HAS MORE THAN ONE CATCH-ALL [E119] -------- guard_defaults.cure

             A variable or `_` pattern matches every value not handled above it, so a later
             catch-all can never be reached.

             at guard_defaults.cure:6:5
             5 |     a -> a
               |     - this earlier pattern already matches every remaining value
             6 |     b -> b
               |     ^ this catch-all is unreachable

             Hint: Keep one final catch-all branch and remove or narrow the others
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 4},
             "end" => %{"line" => 5, "character" => 5}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 4, "character" => 4},
             "end" => %{"line" => 4, "character" => 5}
           }

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "duplicate_default_pattern",
             "name" => "b"
           }

    fixed = String.replace(src, "    b -> b\n", "")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "guard_defaults_fixed.cure")
  end
end
