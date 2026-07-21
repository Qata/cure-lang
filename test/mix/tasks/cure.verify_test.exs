defmodule Mix.Tasks.Cure.VerifyTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    Mix.shell(Mix.Shell.IO)

    dir = Path.join(System.tmp_dir!(), "cure_mix_verify_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "broken.cureproof"), <<0, 1, 2, 3>>)

    on_exit(fn ->
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.verify")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "corrupt proof artifacts use the structured verification diagnostic", %{dir: dir} do
    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.verify")
        assert catch_exit(Mix.Task.run("cure.verify", [dir])) == {:shutdown, 1}
      end)

    assert output =~ "[E066]"
    assert output =~ "Proof verification failed"
    assert output =~ "broken.cureproof"
  end
end
