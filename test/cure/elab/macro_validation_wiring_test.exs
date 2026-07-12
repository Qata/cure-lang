defmodule Cure.Elab.MacroValidationWiringTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "compilation rejects a macro with an uncovered diagnosis point" do
    source = """
    mod M
      macro Every
        syntax every <t: Duration> becomes t
        explain
          keyword "every" =>
            "starts with every"
    """

    assert {:error, {:missing_diagnosis, points}} = Program.elaborate(source)
    assert {:hole_kind, "Duration"} in points
  end

  test "compilation rejects an unpinned syntax rule" do
    source = """
    mod M
      macro Now
        syntax now becomes 0
        explain
          keyword "now" =>
            "starts with now"
    """

    assert {:error, {:rule_unpinned, ["now"]}} = Program.elaborate(source)
  end

  test "compilation rejects a mismatched syntax expansion pin" do
    source = """
    mod M
      macro Now
        syntax now becomes 0
          example now expands 1
        explain
          keyword "now" =>
            "starts with now"
    """

    assert {:error, {:example_mismatch, [%{keyword: "now"}]}} = Program.elaborate(source)
  end

  test "compilation accepts a fully pinned computed rule" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <x: Code> computed by build_it
          example mk 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "mk" =>
            "starts with mk"

      fn build_it(a: MkSyntax) -> Syntax = a.x
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
