defmodule Cure.Compiler.IncrementalHashTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Incremental
  alias Cure.Elab.Program

  test "a real stdlib export_env is serializable and hashes deterministically" do
    {:ok, iface} = Program.module_interface("Std.Core", "lib/std/core.cure")
    h1 = Incremental.interface_hash(iface.export_env)
    h2 = Incremental.interface_hash(iface.export_env)
    assert is_binary(h1) and byte_size(h1) == 32
    assert h1 == h2
  end

  test "different envs hash differently" do
    {:ok, core} = Program.module_interface("Std.Core", "lib/std/core.cure")
    {:ok, list} = Program.module_interface("Std.List", "lib/std/list.cure")
    assert Incremental.interface_hash(core.export_env) != Incremental.interface_hash(list.export_env)
  end
end
