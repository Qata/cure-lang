defmodule Cure.Elab.ModuleInterfaceTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "module_interface/2 returns the export_env and source_hash for a stdlib module" do
    path = "lib/std/core.cure"
    assert {:ok, iface} = Program.module_interface("Std.Core", path)
    assert is_map(iface.export_env)
    assert is_binary(iface.source_hash) and byte_size(iface.source_hash) == 32
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

  test "module_interface/2 surfaces an error for a missing file" do
    assert {:error, _} = Program.module_interface("Nope", "lib/std/does_not_exist.cure")
  end

  test "generated qualified calls load their owner without opening its bare names" do
    caller = Env.empty()
    expression =
      {:function_call, [name: "Std.Bool.not", macro_home_source: "lib/std/example_macro.cure"],
       [{:literal, [subtype: :boolean], true}]}

    generated = Program.env_with_generated_dependencies(caller, expression)

    assert Env.get_def(generated, :"Std.Bool#not")
    assert generated.import_modules == caller.import_modules
  end
end
