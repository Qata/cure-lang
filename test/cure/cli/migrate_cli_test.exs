defmodule Cure.CLI.MigrateCliTest do
  use ExUnit.Case, async: false
  alias Cure.Migrate

  setup do
    dir = Path.join(System.tmp_dir!(), "curemig_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    {_, 0} = System.cmd("git", ["init", "-q", dir])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.email", "t@t"])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.name", "t"])
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "untracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    assert {:error, [{^f, :untracked}]} = Migrate.git_guard([f])
  end

  test "dirty (uncommitted) tracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# changed\n")
    assert {:error, [{^f, :dirty}]} = Migrate.git_guard([f])
  end

  test "staged-only change (index dirty, no worktree diff) is still rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# staged\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    assert {:error, [{^f, :dirty}]} = Migrate.git_guard([f])
  end

  test "clean tracked file passes", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    assert :ok = Migrate.git_guard([f])
  end

  test "a mixed batch reports each file's own reason, not one reason for all", %{dir: dir} do
    # Proves the per-file list shape: one file is untracked, a second is a
    # dirty tracked file, a third is clean -- a single {reason, [path]} pair
    # could not represent "untracked" and "dirty" simultaneously without
    # misreporting one of them.
    untracked_f = Path.join(dir, "untracked.cure")
    dirty_f = Path.join(dir, "dirty.cure")
    clean_f = Path.join(dir, "clean.cure")

    File.write!(dirty_f, "mod D\n")
    File.write!(clean_f, "mod C\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "dirty.cure", "clean.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    File.write!(untracked_f, "mod U\n")
    File.write!(dirty_f, "mod D\n# changed\n")

    assert {:error, reasons} = Migrate.git_guard([untracked_f, dirty_f, clean_f])
    assert {untracked_f, :untracked} in reasons
    assert {dirty_f, :dirty} in reasons
    refute Enum.any?(reasons, &match?({^clean_f, _}, &1))
  end
end
