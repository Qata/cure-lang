# Hardening tests for Cure.Project.set_edition/2 — audit finding F10: a [project]
# header with a trailing comment caused a duplicate table, and the existing-key
# replacement rewrote `edition =` keys in every table, not just [project].
defmodule Cure.ProjectSetEditionTest do
  use ExUnit.Case, async: true

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_setedition_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  defp write_toml(dir, body) do
    path = Path.join(dir, "Cure.toml")
    File.write!(path, body)
    path
  end

  defp project_table_count(out), do: length(Regex.scan(~r/^\s*\[project\]/m, out))

  test "F10a: inserts edition under a [project] header carrying a trailing comment", %{dir: dir} do
    path = write_toml(dir, "[project] # my project\nname = \"x\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    out = File.read!(path)
    assert project_table_count(out) == 1
    assert out =~ ~r/edition = "2026"/
  end

  test "F10b: does not rewrite an edition key living in another table", %{dir: dir} do
    path =
      write_toml(
        dir,
        "[project]\nname = \"x\"\nedition = \"2026\"\n\n[dependencies]\nedition = \"do-not-touch\"\n"
      )

    assert :ok = Cure.Project.set_edition(path, "2027")
    out = File.read!(path)
    assert out =~ ~r/edition = "do-not-touch"/
    assert out =~ ~r/\[project\][\s\S]*edition = "2027"/
    refute out =~ ~r/edition = "2026"/
  end

  test "inserts edition into a plain [project] table that lacks one", %{dir: dir} do
    path = write_toml(dir, "[project]\nname = \"x\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    out = File.read!(path)
    assert out =~ ~r/edition = "2026"/
    assert project_table_count(out) == 1
  end

  test "replaces an existing project edition in place", %{dir: dir} do
    path = write_toml(dir, "[project]\nname = \"x\"\nedition = \"2026\"\n")
    assert :ok = Cure.Project.set_edition(path, "2027")
    out = File.read!(path)
    assert out =~ ~r/edition = "2027"/
    refute out =~ ~r/edition = "2026"/
  end
end
