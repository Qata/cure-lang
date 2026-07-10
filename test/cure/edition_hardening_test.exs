# Hardening tests for Cure.Edition — audit findings F6 (resolve/1 crashes on an
# explicit nil :source) and F8 (compare/2 crashes opaquely on a non-numeric edition).
defmodule Cure.EditionHardeningTest do
  use ExUnit.Case, async: true

  test "F6: resolve/1 tolerates an explicit nil :source and falls back to the default" do
    assert {:ok, edition} = Cure.Edition.resolve(%{source: nil, project_dir: nil})
    assert edition == Cure.Edition.current()
  end

  test "F8: compare/2 raises a clear edition-domain error on a non-numeric input" do
    assert_raise ArgumentError, ~r/edition/, fn ->
      Cure.Edition.compare("abc", "2026")
    end
  end

  test "F8: compare/2 still totally orders valid editions" do
    assert Cure.Edition.compare("2026", "2027") == :lt
    assert Cure.Edition.compare("2027", "2026") == :gt
    assert Cure.Edition.compare("2026", "2026") == :eq
  end
end
