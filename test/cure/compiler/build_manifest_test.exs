defmodule Cure.Compiler.BuildManifestTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.BuildManifest, as: M

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_manifest_test_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "load/1 on an empty dir returns an empty manifest", %{dir: dir} do
    m = M.load(dir)
    assert m.version == 1
    assert m.modules == %{}
    assert m.stdlib_hash == nil
  end

  test "save/1 then load/1 round-trips", %{dir: dir} do
    m = %{
      version: 1,
      toolchain: <<1, 2, 3>>,
      stdlib_hash: <<4, 5>>,
      modules: %{
        "Std.List" => %{
          source_path: "lib/std/list.cure",
          source_hash: <<9>>,
          interface_hash: <<8>>,
          deps: ["Std.Core"],
          beams: ["Cure.Std.List.beam"]
        }
      }
    }

    assert :ok = M.save(m, dir)
    assert M.load(dir) == m
  end

  test "load/1 tolerates a manifest written without stdlib_hash", %{dir: dir} do
    File.write!(
      Path.join(dir, ".cure_manifest"),
      :erlang.term_to_binary(%{version: 1, toolchain: <<7>>, modules: %{}})
    )

    m = M.load(dir)
    assert m.toolchain == <<7>>
    assert m.stdlib_hash == nil
  end

  test "load/1 on a corrupt manifest returns empty, never raises", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), "not a term <<<")
    assert M.load(dir).modules == %{}
  end

  test "load/1 on a wrong-version manifest returns empty", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), :erlang.term_to_binary(%{version: 999, toolchain: "", modules: %{}}))
    assert M.load(dir).modules == %{}
  end

  test "save/1 is atomic — no .tmp file is left behind", %{dir: dir} do
    assert :ok = M.save(M.empty(<<0>>), dir)
    refute File.exists?(Path.join(dir, ".cure_manifest.tmp"))
  end

  test "toolchain_fingerprint/0 is a stable 32-byte digest" do
    a = M.toolchain_fingerprint()
    b = M.toolchain_fingerprint()
    assert is_binary(a) and byte_size(a) == 32
    assert a == b
  end

  test "artifact fingerprint excludes presentation and tooling beams" do
    refute M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Diagnostic.Adapter.Name.beam")
    refute M.semantic_toolchain_beam?("/tmp/Elixir.Cure.CLI.beam")
    refute M.semantic_toolchain_beam?("/tmp/Elixir.Antigen.Cover.beam")
    refute M.semantic_toolchain_beam?("/tmp/Elixir.Mix.Tasks.Cure.Compile.beam")
  end

  test "artifact fingerprint retains semantic compiler beams" do
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Compiler.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Core.Kernel.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Elab.Program.beam")
    assert M.semantic_toolchain_beam?("/tmp/Elixir.Cure.Project.beam")
  end
end
