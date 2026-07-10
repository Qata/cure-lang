defmodule Cure.EditionTest do
  use ExUnit.Case, async: true
  alias Cure.Edition

  test "current is the newest known edition and is valid" do
    assert Edition.current() == "2026"
    assert Edition.valid?("2026")
    assert Edition.all() == ["2026"]
  end

  test "parse accepts a known edition and rejects an unknown one" do
    assert Edition.parse("2026") == {:ok, "2026"}
    assert Edition.parse("2062") == {:error, {:unknown_edition, "2062"}}
  end

  test "compare orders editions by integer year" do
    assert Edition.compare("2026", "2026") == :eq
    # a hypothetical newer edition compares greater (compare must not itself
    # gate on the allow-list, so ordering logic is testable ahead of minting)
    assert Edition.compare("2025", "2026") == :lt
    assert Edition.compare("2027", "2026") == :gt
  end
end
