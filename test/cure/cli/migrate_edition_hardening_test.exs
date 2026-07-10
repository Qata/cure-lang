# Hardening tests for the migrate CLI — audit findings F9 (bump pragma regex
# looser than Edition → crash) and F4 (downgrade guard must measure against the
# project edition). F4/F5's end-to-end downgrade path is unreachable with a single
# minted edition (the --edition flag is allow-list-validated first, and
# Project.load rejects an unknown edition), so this covers the reachable units.
defmodule Cure.CLI.MigrateEditionHardeningTest do
  use ExUnit.Case, async: true

  test "F9: migrate_edition_pragma accepts a 4-digit year and rejects malformed values" do
    assert Cure.CLI.migrate_edition_pragma("@edition(\"2026\")\nmod M\n") == "2026"
    assert Cure.CLI.migrate_edition_pragma("@edition(\"abc\")\nmod M\n") == nil
    assert Cure.CLI.migrate_edition_pragma("@edition(2026)\nmod M\n") == nil
    assert Cure.CLI.migrate_edition_pragma("@edition(\"20260\")\nmod M\n") == nil
    assert Cure.CLI.migrate_edition_pragma("mod M\n") == nil
  end

  test "F4: migrate_project_edition falls back to current() when no project is present" do
    dir = Path.join(System.tmp_dir!(), "cure_noproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    assert Cure.CLI.migrate_project_edition(dir) == {:ok, Cure.Edition.current()}
  end

  test "F4: migrate_project_edition reads a declared [project].edition" do
    dir = Path.join(System.tmp_dir!(), "cure_proj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    # Uses the one minted edition; confirms the helper resolves the project value
    # (not a crash / not something else) even though it equals current() today.
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"2026\"\n")
    assert Cure.CLI.migrate_project_edition(dir) == {:ok, "2026"}
  end

  # I4 (audit iteration 2): a Cure.toml declaring an edition the compiler does
  # not know must be SURFACED, not masked as current() — masking would let a
  # broken project edition wave through a real downgrade. "1999" is guaranteed
  # off the known-editions allow-list.
  test "I4: migrate_project_edition surfaces an unknown declared edition" do
    dir = Path.join(System.tmp_dir!(), "cure_badproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"1999\"\n")
    assert Cure.CLI.migrate_project_edition(dir) == {:error, {:unknown_edition, "1999"}}
  end

  # The pure downgrade comparison honours the passed :current (this is what the
  # F4 wiring feeds the project edition into). compare/2 is allow-list-independent,
  # so a hypothetical older/newer edition is a valid probe.
  test "F4/F5: plan_migration refuses a target older than :current and accepts otherwise" do
    assert {:error, :downgrade} = Cure.CLI.plan_migration(target: "2026", current: "2027")
    assert {:ok, "2027"} = Cure.CLI.plan_migration(target: "2027", current: "2026")
    assert {:ok, "2026"} = Cure.CLI.plan_migration(target: "2026", current: "2026")
  end
end
