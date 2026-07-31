defmodule Mix.Tasks.Cure.Check.DocsTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    previous_cwd = File.cwd!()
    Mix.shell(Mix.Shell.IO)

    root = Path.join(System.tmp_dir!(), "cure_check_docs_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(root, "priv/doc_snippets"))
    File.write!(Path.join(root, "priv/doc_snippets/support.cure"), "")

    # The task resolves the stdlib as `_build/cure/ebin` relative to the project
    # root. Without one, artifact verification rejects every snippet with E100
    # before it is judged, and each test fails for a reason it is not testing.
    File.mkdir_p!(Path.join(root, "_build/cure"))
    File.ln_s!(Path.join(previous_cwd, "_build/cure/ebin"), Path.join(root, "_build/cure/ebin"))

    System.cmd("git", ["init", "--quiet"], cd: root)
    File.cd!(root)

    on_exit(fn ->
      File.cd!(previous_cwd)
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.check.docs")
      File.rm_rf!(root)
    end)

    {:ok, root: root}
  end

  test "compiles every tracked Cure fence and ignores other languages", %{root: root} do
    write_and_track(root, "GUIDE.md", """
    ```cure
    fn answer() -> Int = 42
    ```

    ```elixir
    not_cure()
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  GUIDE.md:2"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "no tag opts a cure fence out of checking, but a text fence is not one", %{root: root} do
    write_and_track(root, "NOT_CODE.md", """
    ```cure pseudocode
    match xs
      [] -> 0
    ```

    ```text
    match xs
      [] -> 0
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", ["--verbose"])) == {:shutdown, 1}
        end)
      end)

    # The `cure` fence is checked despite its tag; the `text` fence below it is
    # never extracted, so exactly one snippet is judged.
    assert output =~ "FAIL NOT_CODE.md:2"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "compiles Cure fences embedded in tracked .cure docstrings", %{root: root} do
    write_and_track(root, "demo.cure", """
    mod Demo
      ## ## Examples
      ##
      ## ```cure expr
      ## 40 + 2
      ## ```
      fn answer() -> Int = 42
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  demo.cure:5"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "compiles independent expressions in one fence", %{root: root} do
    write_and_track(root, "LITERALS.md", """
    ```cure
    1 + 1
    true
    :ok
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", [])
      end)

    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "fails with the Markdown path and authored fence line", %{root: root} do
    write_and_track(root, "BROKEN.md", """
    prose

    ```cure
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        ExUnit.CaptureIO.capture_io(fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert stderr =~ "UNKNOWN VALUE [E091]"
    assert stderr =~ "BROKEN.md"
    assert stderr =~ "missing"
  end

  test "rejects command arguments before scanning" do
    Mix.Task.reenable("cure.check.docs")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.check.docs", ["unexpected"])) == {:shutdown, 1}
      end)

    assert stderr =~ "INVALID COMMAND USAGE [E099]"
    assert stderr =~ "Usage: mix cure.check.docs"
  end

  test "an error-tagged fence passes only for the expected diagnostic", %{root: root} do
    write_and_track(root, "NEGATIVE.md", """
    ```cure E091
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  NEGATIVE.md:2 (E091 as documented)"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "an error-tagged fence fails when it unexpectedly compiles", %{root: root} do
    write_and_track(root, "STALE_NEGATIVE.md", """
    ```cure E091
    fn answer() -> Int = 42
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
      end)

    assert output =~ "expected E091 but compiled"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "an error-tagged fence fails on a different diagnostic", %{root: root} do
    write_and_track(root, "WRONG_ERROR.md", """
    ```cure E003
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert output =~ "expected E003, got E091"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "a warning-tagged fence passes when the documented warning is emitted", %{root: root} do
    write_and_track(root, "WARNS.md", """
    ```cure W000
    #{deprecated_extern()}
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  WARNS.md:2 (W000 as documented)"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "a warning-tagged fence fails when the snippet compiles cleanly", %{root: root} do
    write_and_track(root, "STALE_WARNING.md", """
    ```cure W000
    fn answer() -> Int = 42
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
      end)

    assert output =~ "expected W000 but compiled without warnings"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "a warning-tagged fence fails when the snippet does not compile", %{root: root} do
    write_and_track(root, "BROKEN_WARNING.md", """
    ```cure W000
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert output =~ "expected W000, got E091"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "an untagged fence still fails on any warning", %{root: root} do
    write_and_track(root, "UNDECLARED_WARNING.md", """
    ```cure
    #{deprecated_extern()}
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert output =~ "UNDECLARED_WARNING.md:2 (1 warning(s))"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  # A snippet that compiles while emitting exactly one W000. `erlang:now/0` has
  # been deprecated since OTP 18, so the Erlang linter warns without any Cure
  # standard library being reachable from the temporary project root.
  defp deprecated_extern do
    """
    @extern(:erlang, :now, 0)
    fn timestamp() -> Int
    """
    |> String.trim_trailing()
  end

  defp write_and_track(root, relative, contents) do
    path = Path.join(root, relative)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, contents)
    System.cmd("git", ["add", "--", relative], cd: root)
  end
end
