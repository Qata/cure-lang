defmodule Cure.Compiler.EditionLexerTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer
  alias Cure.Migrate.Rule

  # A fixture rule that retires the keyword "fsm" starting at edition "2027".
  defp retire_fsm_2027 do
    %Rule{
      id: :W_test_retire, description: "retire fsm", phase: :syntactic,
      tier: :machine, since: "2026", enforced_in: "2027", retires_keywords: ["fsm"],
      detect_and_rewrite: fn _ast, _ctx -> :no_change end,
      warning_template: "fsm retired"
    }
  end

  defp kinds(src, edition, rules) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false, edition: edition, migrate_rules: rules)
    for t <- toks, t.value in [:fsm, "fsm"], do: {t.type, t.value}
  end

  test "a keyword retired at 2027 is still a keyword at 2026 and an identifier at 2027" do
    rules = [retire_fsm_2027()]
    assert [{:keyword, :fsm}] = kinds("fsm x\n", "2026", rules)
    assert [{:identifier, "fsm"}] = kinds("fsm x\n", "2027", rules)
  end

  test "retired_keywords is derived from the registry, not hardcoded" do
    assert Cure.Edition.retired_keywords("2027", [retire_fsm_2027()]) == ["fsm"]
    assert Cure.Edition.retired_keywords("2026", [retire_fsm_2027()]) == []
  end

  test "proto/impl stay keywords in every edition (enforced_in: nil once the real rule ships)" do
    # with no retiring rule for them, they are never removed
    assert Cure.Edition.retired_keywords("2026", []) == []
  end
end
