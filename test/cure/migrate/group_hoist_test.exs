defmodule Cure.Migrate.GroupHoistTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp reparses?(src, file) do
    with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
         {:ok, _ast} <- Parser.parse(toks, file: file, emit_events: false) do
      true
    else
      _ -> false
    end
  end

  defp migrate(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(Trivia.attach(ast, trivia), file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  test "in-body @group is hoisted to directly above mod and output reparses" do
    {out, warns} = migrate("mod M\n@group(:core)\nfn f() -> Int = 1\n", "a.cure")
    # decorator now appears before `mod`, and not after it
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+M/
    refute out =~ ~r/mod\s+M[\s\S]*@group\(:core\)/
    assert Enum.any?(warns, &(&1.rule == :W_group_hoist))
    assert reparses?(out, "a.cure")
  end

  test "a file already in above-mod form is unchanged and does not warn" do
    src = "@group(:core)\nmod M\nfn f() -> Int = 1\n"
    {out, warns} = migrate(src, "b.cure")
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+M/
    refute Enum.any?(warns, &(&1.rule == :W_group_hoist))
  end

  test "a comment on the @group line travels with the hoisted decorator (never dropped or orphaned)" do
    {out, _} = migrate("mod M\n@group(:core)  # grouping tag\nfn f() -> Int = 1\n", "c.cure")
    # the comment survives...
    assert out =~ "grouping tag"
    # ...and rides above mod with the decorator, not left stranded below it
    assert out =~ ~r/@group\(:core\).*grouping tag[\s\S]*mod\s+M/
    refute out =~ ~r/mod\s+M[\s\S]*grouping tag/
    assert reparses?(out, "c.cure")
  end

  test "a @group under a later module hoists above THAT module, not the first" do
    # Multi-module files parse and compile; migrate runs on source syntactically.
    # The `@group(:core)` belongs to `Second` (it trails Second's `mod`), so it
    # must hoist above `Second`. The rule keyed every mover to the FIRST module,
    # silently re-associating the group with `First` — a semantic corruption that
    # `verify/3` accepts (the output reparses, comments preserved).
    src = "mod First\nfn f() -> Int = 1\nmod Second\n@group(:core)\nfn g() -> Int = 2\n"
    {out, warns} = migrate(src, "multi.cure")

    assert Enum.any?(warns, &(&1.rule == :W_group_hoist))
    # @group sits directly above Second...
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+Second/
    # ...and NOT above First (no @group between the start and `mod First`).
    refute out =~ ~r/@group\(:core\)[\s\S]*mod\s+First/
    assert reparses?(out, "multi.cure")
  end

  test "each @group hoists above its own module in a two-module, two-group file" do
    src =
      "mod First\n@group(:a)\nfn f() -> Int = 1\nmod Second\n@group(:b)\nfn g() -> Int = 2\n"

    {out, _} = migrate(src, "two.cure")

    assert out =~ ~r/@group\(:a\)\s*\n\s*mod\s+First/
    assert out =~ ~r/@group\(:b\)\s*\n\s*mod\s+Second/
    # neither group landed above the wrong module (both stacked above First was
    # the bug symptom)
    refute out =~ ~r/@group\(:b\)[\s\S]*mod\s+First/
    assert reparses?(out, "two.cure")
  end
end
