defmodule Mix.Tasks.Cure.CompileTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    Mix.shell(Mix.Shell.Process)

    dir = Path.join(System.tmp_dir!(), "cure_mix_compile_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn ->
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.compile")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "directory compilation propagates a user prelude operator through the real task", %{dir: dir} do
    suffix = System.unique_integer([:positive])
    provider = "MixFixityProvider#{suffix}"
    consumer = "MixFixityConsumer#{suffix}"

    File.write!(Path.join(dir, "provider.cure"), """
    @prelude
    mod #{provider}
      precedencegroup MixFixityGroup#{suffix}
        associativity: left
      infix `<?>` : MixFixityGroup#{suffix}
      fn `<?>`(a: Int, b: Int) -> Int = a
    end
    """)

    File.write!(Path.join(dir, "consumer.cure"), """
    mod #{consumer}
      fn go() -> Int = 41 <?> 1
    end
    """)

    out = Path.join(dir, "ebin")
    Mix.Task.reenable("cure.compile")
    assert :ok = Mix.Task.run("cure.compile", [dir, "--output-dir", out])

    assert apply(String.to_atom("Cure.#{consumer}"), :go, []) == 41
  end

  test "compile diagnostics render through the shared sink", %{dir: dir} do
    path = Path.join(dir, "bad.cure")
    out = Path.join(dir, "ebin")
    File.write!(path, "fn run() -> Int = missing_name\n")
    Mix.shell(Mix.Shell.IO)
    Mix.Task.reenable("cure.compile")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert :ok = Mix.Task.run("cure.compile", [path, "--output-dir", out])
      end)

    assert output =~ "[E091]"
    assert output =~ "missing_name"
    assert output =~ "^^^^^^^^^^^^"
    refute output =~ "{:unknown_global"
  end

  test "bare branch verdicts keep their branch-specific title in the Mix task", %{dir: dir} do
    path = Path.join(dir, "bad_branch.cure")
    out = Path.join(dir, "ebin_branch")

    File.write!(path, """
    mod BadBranch
      type Flag = On | Off
      fn run(flag: Flag) -> Int = match flag
        On -> 1
        Off -> true
    end
    """)

    Mix.shell(Mix.Shell.IO)
    Mix.Task.reenable("cure.compile")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert :ok = Mix.Task.run("cure.compile", [path, "--output-dir", out])
      end)

    assert output =~ "PATTERN BRANCHES DISAGREE"
    refute output =~ "ELABORATION FAILED"
  end
end
