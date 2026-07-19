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
end
