defmodule Cure.Elab.ModuleInterfaceTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.ModuleInterface
  alias Cure.Elab.Program

  @moduletag :tmp_dir

  test "module_interface/2 returns the export_env and source_hash for a stdlib module" do
    path = "lib/std/core.cure"
    assert {:ok, %ModuleInterface{} = iface} = Program.module_interface("Std.Core", path)
    assert is_map(iface.export_env)
    assert is_binary(iface.source_hash) and byte_size(iface.source_hash) == 32
    assert is_binary(iface.interface_hash) and byte_size(iface.interface_hash) == 32
    assert :ok = ModuleInterface.validate(iface)
  end

  test "dependency interface identities are canonical and complete" do
    assert {:ok, %ModuleInterface{} = iface} =
             Program.module_interface("Std.Regex", "lib/std/regex.cure")

    assert iface.dependency_interface_hashes != %{}

    assert Enum.all?(iface.dependency_interface_hashes, fn {module_name, hash} ->
             is_binary(module_name) and is_binary(hash) and byte_size(hash) == 32
           end)

    assert Enum.sort(Map.keys(iface.dependency_interface_hashes)) ==
             Enum.sort(iface.dependency_names)
  end

  test "module_interface/2 is a cache hit after priming (identical stored term)" do
    path = "lib/std/core.cure"
    # Prime: the first call computes and `:persistent_term.put`s the interface,
    # returning the freshly-computed heap term (put keeps the original, get hands
    # back the off-heap copy — so a compute call is never `:erts_debug.same` as a
    # later read). Every call thereafter is a pure cache read.
    assert {:ok, _primed} = Program.module_interface("Std.Core", path)
    assert {:ok, a} = Program.module_interface("Std.Core", path)
    assert {:ok, b} = Program.module_interface("Std.Core", path)
    # Two cache reads of the same key return the identical off-heap term, proving
    # the stdlib interface is served from the persistent_term cache, not recomputed.
    assert :erts_debug.same(a, b)
  end

  test "concurrent cold prelude-manifest readers share one completed value" do
    Program.invalidate_prelude_manifest()

    manifests =
      1..32
      |> Task.async_stream(
        fn _ -> Program.prelude_manifest() end,
        max_concurrency: 32,
        timeout: 30_000,
        ordered: false
      )
      |> Enum.map(fn {:ok, manifest} -> manifest end)

    assert [first | rest] = manifests
    assert first != []
    assert Enum.all?(rest, &(&1 == first))
    assert Program.prelude_manifest() == first
  end

  test "a fresh in-memory loader reuses the fingerprinted interface artifact" do
    path = Path.expand("lib/std/core.cure")
    cache_key = {Program, :module_interface, path}

    assert {:ok, primed} = Program.module_interface("Std.Core", path)
    :persistent_term.erase(cache_key)
    Process.put(:cure_module_loader_observer, self())

    on_exit(fn ->
      Process.delete(:cure_module_loader_observer)
    end)

    assert {:ok, cached} = Program.module_interface("Std.Core", path)
    assert cached == primed
    refute_received {:cure_module_loader, {:compiling, "Std.Core", ^path}}
  end

  test "module_interface/2 surfaces an error for a missing file" do
    assert {:error, _} = Program.module_interface("Nope", "lib/std/does_not_exist.cure")
  end

  test "interface dependency edges retain their authored kind and source line", %{tmp_dir: dir} do
    path = Path.join(dir, "interface_edges.cure")

    File.write!(path, """
    mod InterfaceEdges

      use Std.Nat
      fn count() -> Int = Std.Int.negate(1)
    """)

    assert {:ok, interface} = Program.module_interface("InterfaceEdges", path)

    assert Enum.map(interface.direct_edges, &{&1.kind, &1.target, &1.line}) == [
             {:qualified_reference, "Std.Int", 4},
             {:use_import, "Std.Nat", 3}
           ]
  end
end
