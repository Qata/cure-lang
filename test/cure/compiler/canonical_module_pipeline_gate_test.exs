defmodule Cure.Compiler.CanonicalModulePipelineGateTest do
  use ExUnit.Case, async: true

  defp selection(function, arguments),
    do: apply(Cure.Compiler.ModulePipeline.Selection, function, arguments)

  defp request(function, arguments),
    do: apply(Cure.Compiler.ModulePipeline.Request, function, arguments)

  test "the gate has one explicit canonical spelling" do
    assert {:ok, :default} = selection(:normalize, [[]])
    assert {:ok, :canonical} = selection(:normalize, [[module_pipeline: :canonical]])

    for invalid <- [:existing, :new, :v2, "canonical", true, false] do
      assert {:error, {:invalid_module_pipeline, ^invalid}} =
               selection(:normalize, [[module_pipeline: invalid]])
    end
  end

  test "a request owns normalized semantic inputs without process state" do
    assert {:ok, value} =
             request(:new, [
               [
                 module_pipeline: :canonical,
                 entry_point: :compiler_file,
                 package: "app",
                 sources: ["lib/app.cure"],
                 source_roots: ["lib"],
                 interface_roots: ["deps/interfaces"],
                 output_root: "_build/cure"
               ]
             ])

    assert value.selection == :canonical
    assert value.entry_point == :compiler_file
    assert value.package == "app"
    assert value.sources == ["lib/app.cure"]
    assert value.source_roots == ["lib"]
    assert value.interface_roots == ["deps/interfaces"]
    assert value.output_root == "_build/cure"
  end

  test "child requests inherit the canonical selection and cannot downgrade" do
    assert {:ok, parent} =
             request(:new, [[module_pipeline: :canonical, entry_point: :compiler_files]])

    assert {:ok, child} = request(:child, [parent, [entry_point: :macro_check]])
    assert child.selection == :canonical
    assert child.entry_point == :macro_check

    assert {:error, {:module_pipeline_mismatch, :canonical, :default}} =
             request(:child, [parent, [module_pipeline: nil, entry_point: :macro_check]])
  end

  test "unknown request fields fail rather than disappearing" do
    assert {:error, {:unknown_module_pipeline_options, [:mystery]}} =
             request(:new, [[entry_point: :compiler_file, mystery: true]])
  end
end
