defmodule Cure.ProjectEditionTest do
  use ExUnit.Case, async: true

  defp write_toml(body) do
    dir = Path.join(System.tmp_dir!(), "cureproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "Cure.toml"), body)
    dir
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
