defmodule Mix.Tasks.Cure.BundleStdlibBeamsTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Mix.Tasks.Cure.BundleStdlibBeams

  describe "default_destination/0" do
    test "points at priv/ebin relative to the current project" do
      assert BundleStdlibBeams.default_destination() == Path.join(["priv", "ebin"])
    end
  end

  describe "bundle/2" do
    test "no-op when the source directory does not exist" do
      src = Path.join(System.tmp_dir!(), "cure_bundle_beams_missing_#{unique()}")
      dst = make_tmp!()

      assert {:ok, %{compiled: 0, skipped: 0, errors: 0}} = BundleStdlibBeams.bundle(src, dst)
      assert File.ls!(dst) == []
    after
      cleanup_tmps()
    end

    # We do not exercise the success path directly here because it
    # depends on `Cure.Compiler` being fully wired up, which the
    # integration-style tests in `test/cure/stdlib/preload_test.exs`
    # already cover end-to-end. Keeping this test module focused on
    # the pure helpers keeps it fast and isolated.

    test "dependency order wins over filename order for cross-module calls" do
      # Regression: `bundle/2` must compile in dependency order, not filename
      # order, and each
      # module's import resolver (`module_exports?`) probes the *loaded*
      # version of an imported module. If a freshly-compiled beam is not
      # loaded into the VM before the next module compiles, the probe hits
      # a stale/absent module and the cross-module @extern call falls back
      # to a local call -> `{:undefined_function, ...}` -> the dependent
      # module fails to compile. The bundle must load each fresh beam so
      # later modules see its exports. (Std.Comparable -> Std.Char.code_point.)
      src = make_tmp!()
      dst = make_tmp!()

      write_cure!(src, "z_helper.cure", """
      mod Std.TcaHelper
        @extern(:erlang, :abs, 1)
        fn ext_helper(x: Int) -> Int
      """)

      write_cure!(src, "a_user.cure", """
      mod Std.TcaUser
        use Std.TcaHelper
        fn use_it(x: Int) -> Int = ext_helper(x)
      """)

      assert {:ok, %{errors: 0}} = BundleStdlibBeams.bundle(src, dst)
      assert {:ok, set} = Cure.Compiler.Artifacts.open_verified_set(dst)
      assert File.exists?(Path.join(set.artifact_root, "Cure.Std.TcaUser.beam"))
    after
      :code.purge(:"Cure.Std.TcaHelper")
      :code.delete(:"Cure.Std.TcaHelper")
      cleanup_tmps()
    end

    test "a skipped dependency is loaded before a changed consumer compiles" do
      src = make_tmp!()
      dst = make_tmp!()

      write_cure!(src, "z_helper.cure", """
      mod Std.TcaSkippedHelper
        @extern(:erlang, :abs, 1)
        fn ext_helper(x: Int) -> Int
      """)

      write_cure!(src, "a_user.cure", """
      mod Std.TcaSkippedUser
        use Std.TcaSkippedHelper
        fn use_it(x: Int) -> Int = ext_helper(x)
      """)

      assert {:ok, %{errors: 0}} = BundleStdlibBeams.bundle(src, dst)

      :code.purge(:"Cure.Std.TcaSkippedHelper")
      :code.delete(:"Cure.Std.TcaSkippedHelper")

      write_cure!(src, "a_user.cure", """
      mod Std.TcaSkippedUser
        use Std.TcaSkippedHelper
        fn use_it(x: Int) -> Int = ext_helper(x) + 0
      """)

      assert {:ok, %{compiled: 1, skipped: 1, errors: 0}} =
               BundleStdlibBeams.bundle(src, dst)

      assert {:ok, set} = Cure.Compiler.Artifacts.open_verified_set(dst)
      assert File.exists?(Path.join(set.artifact_root, "Cure.Std.TcaSkippedHelper.beam"))
    after
      :code.purge(:"Cure.Std.TcaSkippedHelper")
      :code.delete(:"Cure.Std.TcaSkippedHelper")
      cleanup_tmps()
    end

    test "renders the underlying structured diagnostic when a module fails" do
      src = make_tmp!()
      dst = make_tmp!()

      path =
        write_cure!(src, "broken.cure", """
        mod Std.Broken
          fn broken() -> Int = missing_value
        """)

      output =
        capture_io(:stderr, fn ->
          assert {:error, {:artifact_sweep_failed, [_]}} =
                   BundleStdlibBeams.bundle(src, dst)
        end)

      assert output =~ "UNKNOWN VALUE [E091]"
      assert output =~ "`missing_value` is not available"
      assert output =~ path
      assert output =~ "fn broken() -> Int = missing_value"
      assert output =~ "^^^^^^"
    after
      cleanup_tmps()
    end
  end

  # ---------------------------------------------------------------------------

  defp make_tmp! do
    path = Path.join(System.tmp_dir!(), "cure_bundle_beams_test_#{unique()}")
    File.mkdir_p!(path)
    Process.put(:cleanup, [path | Process.get(:cleanup, [])])
    path
  end

  defp cleanup_tmps do
    Process.get(:cleanup, []) |> Enum.each(&File.rm_rf!/1)
    Process.put(:cleanup, [])
  end

  defp write_cure!(dir, name, contents) do
    path = Path.join(dir, name)
    File.write!(path, contents)
    path
  end

  defp unique, do: System.unique_integer([:positive])
end
