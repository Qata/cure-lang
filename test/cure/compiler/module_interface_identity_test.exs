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

  test "source and dependency hashes are validation metadata, not public identity" do
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

    refute original.source_hash == changed_source.source_hash
    assert original.interface_hash == changed_source.interface_hash
    assert original.interface_hash == changed_dependency.interface_hash
    refute original.dependency_interface_hashes == changed_dependency.dependency_interface_hashes
  end

  test "cyclic dependency metadata does not recursively perturb public identities" do
    left =
      ModuleInterface.new(%{
        module_name: "Left",
        source_path: "left.cure",
        source_hash: <<1>>,
        dependency_interface_hashes: %{"Right" => <<10>>},
        canonical_declarations: %{definitions: %{:"Left#value" => %{arity: 0}}}
      })

    right =
      ModuleInterface.new(%{
        module_name: "Right",
        source_path: "right.cure",
        source_hash: <<2>>,
        dependency_interface_hashes: %{"Left" => left.interface_hash},
        canonical_declarations: %{definitions: %{:"Right#value" => %{arity: 0}}}
      })

    left_again =
      left
      |> Map.from_struct()
      |> Map.merge(%{
        dependency_interface_hashes: %{"Right" => right.interface_hash},
        interface_hash: nil
      })
      |> ModuleInterface.new()

    assert left_again.interface_hash == left.interface_hash
  end

  test "diagnostic edge locations do not perturb semantic identity" do
    base = %{
      module_name: "Canonical.Provider",
      source_path: "provider.cure",
      source_hash: <<1>>,
      dependency_interface_hashes: %{"Canonical.Base" => <<2>>},
      direct_edges: [%{kind: :use_import, target: "Canonical.Base", line: 2}]
    }

    shifted =
      base
      |> Map.put(:source_hash, <<3>>)
      |> Map.put(:direct_edges, [%{kind: :use_import, target: "Canonical.Base", line: 20}])

    left = ModuleInterface.new(base)
    right = ModuleInterface.new(shifted)

    assert left.interface_hash == right.interface_hash
    refute left.direct_edges == right.direct_edges
  end
end
