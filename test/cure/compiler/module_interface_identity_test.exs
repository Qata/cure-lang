defmodule Cure.Compiler.ModuleInterfaceIdentityTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.ModuleInterface

  test "semantic identity is deterministic and independent of transitional environments" do
    attrs = %{
      module_name: "Canonical.Provider",
      source_path: "provider.cure",
      source_hash: :crypto.hash(:sha256, "source"),
      dependency_interface_hashes: %{"Canonical.Base" => <<1, 2, 3>>},
      direct_edges: [
        %{kind: :use_import, target: "Canonical.Base", line: 2}
      ],
      canonical_declarations: %{definitions: %{:"Canonical.Provider#value" => %{arity: 0}}}
    }

    left = ModuleInterface.new(Map.put(attrs, :export_env, %{transitional: :left}))
    right = ModuleInterface.new(Map.put(attrs, :export_env, %{transitional: :right}))

    assert left.interface_hash == right.interface_hash
    assert left.dependency_interface_hashes == right.dependency_interface_hashes
    assert :ok = ModuleInterface.validate(left)
    assert :ok = ModuleInterface.validate(right)
  end

  test "source and dependency identity both invalidate an interface" do
    base = %{
      module_name: "Canonical.Provider",
      source_path: "provider.cure",
      source_hash: <<1>>,
      dependency_interface_hashes: %{"Canonical.Base" => <<2>>}
    }

    original = ModuleInterface.new(base)
    changed_source = ModuleInterface.new(%{base | source_hash: <<3>>})

    changed_dependency =
      ModuleInterface.new(%{base | dependency_interface_hashes: %{"Canonical.Base" => <<4>>}})

    refute original.interface_hash == changed_source.interface_hash
    refute original.interface_hash == changed_dependency.interface_hash
  end
end
