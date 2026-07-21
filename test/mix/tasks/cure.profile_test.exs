defmodule Mix.Tasks.Cure.ProfileTest do
  use ExUnit.Case, async: false

  test "compile failures render through the structured source-aware diagnostic" do
    path = Path.join(System.tmp_dir!(), "cure_profile_bad_#{System.unique_integer([:positive])}.cure")
    File.write!(path, "fn run() -> Int = missing_name\n")

    on_exit(fn -> File.rm(path) end)

    Mix.Task.reenable("cure.profile")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.run("cure.profile", [path])
      end)

    assert stderr =~ "[E091]"
    assert stderr =~ "missing_name"
    assert stderr =~ "^^^^^^^^^^^^"
    refute stderr =~ "{:unknown_global"
  end
end
