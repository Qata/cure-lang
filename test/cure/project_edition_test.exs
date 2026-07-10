defmodule Cure.ProjectEditionTest do
  use ExUnit.Case, async: true

  defp write_toml(body) do
    dir = Path.join(System.tmp_dir!(), "cureproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "Cure.toml"), body)
    dir
  end

  # find_root/1 (iteration 5): locate the nearest ancestor Cure.toml from a file
  # path so the compile boundary can honour a project's edition without every CLI
  # caller threading a project dir.
  test "find_root returns the directory of the nearest ancestor Cure.toml" do
    dir = write_toml("[project]\nname = \"demo\"\nedition = \"2026\"\n")
    sub = Path.join([dir, "a", "b"])
    File.mkdir_p!(sub)
    assert Cure.Project.find_root(Path.join(sub, "x.cure")) == Path.expand(dir)
  end

  test "find_root returns the NEAREST manifest when nested (child shadows parent)" do
    parent = write_toml("[project]\nname = \"outer\"\nedition = \"2026\"\n")
    child = Path.join(parent, "inner")
    File.mkdir_p!(child)
    File.write!(Path.join(child, "Cure.toml"), "[project]\nname = \"inner\"\n")
    assert Cure.Project.find_root(Path.join(child, "x.cure")) == Path.expand(child)
  end

  test "find_root returns nil when no ancestor holds a Cure.toml (no loop at fs root)" do
    dir = Path.join(System.tmp_dir!(), "cure_noroot_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    assert Cure.Project.find_root(Path.join(dir, "x.cure")) == nil
  end

  test "find_root(nil) is nil (headless source with no file)" do
    assert Cure.Project.find_root(nil) == nil
  end

  test "loads a validated edition from the [project] table" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2026\"\n")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  test "absent edition key yields nil (the default path is applied at resolution, not load)" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\n")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == nil
  end

  test "an unknown edition in the manifest is a load-time error" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2062\"\n")
    assert {:error, {:unknown_edition, "2062"}} = Cure.Project.load(dir)
  end
end
