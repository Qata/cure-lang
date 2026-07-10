defmodule Cure.Audit.TrustCLITest do
  use ExUnit.Case, async: true
  alias Cure.Audit.{CLI, Source}

  test "locates a stdlib module by its mod header, not its filename" do
    assert {:ok, path} = Source.locate("Std.NonEmpty")
    assert Path.basename(path) == "non_empty.cure"

    assert {:ok, path} = Source.locate("Std.CRDT")
    assert Path.basename(path) == "crdt.cure"
  end

  test "an unknown module is not found" do
    assert Source.locate("Std.NoSuchModule") == {:error, :not_found}
  end

  test "CLI.run propagates a locate miss, which is what the halt(1) clause needs" do
    assert CLI.run("Std.NoSuchModule", []) == {:error, :not_found}
  end

  test "Std.List produces a report and does not fail --strict" do
    assert {:ok, text} = CLI.run("Std.List", [])
    assert text =~ "AXIOMS — OTP (1)"
    assert text =~ "UNAUDITED (0)"
    assert {:ok, _} = CLI.run("Std.List", strict: true)
  end

  test "Std.Time does not elaborate, so it lands in UNAUDITED" do
    assert {:ok, text} = CLI.run("Std.Time", [])
    assert text =~ "UNAUDITED (1)"
    assert text =~ "Std.Time"
  end

  test "--strict fails iff UNAUDITED is non-empty" do
    assert {:strict_failure, _} = CLI.run("Std.Time", strict: true)
    assert {:ok, _} = CLI.run("Std.Time", [])
  end

  test "--target adds the section; its absence omits it" do
    {:ok, with_target} = CLI.run("Std.List", target: :atomvm)
    {:ok, without} = CLI.run("Std.List", [])
    assert with_target =~ "UNAVAILABLE ON TARGET"
    refute without =~ "UNAVAILABLE ON TARGET"
  end

  test "two runs are byte-identical" do
    {:ok, a} = CLI.run("Std.List", [])
    {:ok, b} = CLI.run("Std.List", [])
    assert a == b
  end
end
