defmodule Cure.Diagnostic.RegistryTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Registry

  test "every catalog code has typed ownership and schema metadata" do
    catalog_codes = Cure.Compiler.Errors.list_all() |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    entries = Registry.entries()

    assert Enum.map(entries, & &1.code) |> Enum.sort() == catalog_codes
    assert Enum.all?(entries, &(&1.status in [:reachable, :retired]))
    assert Enum.all?(entries, &(is_atom(&1.subsystem) and &1.payload_schema == 1))
    assert Enum.all?(entries, &is_atom(&1.key))
    assert Enum.all?(entries, &(is_integer(&1.schema_version) and &1.schema_version >= 1))
    assert Enum.all?(entries, &(is_list(&1.producers) and &1.producers != []))

    assert Enum.all?(entries, fn entry ->
             is_atom(entry.converter) and is_atom(entry.converter_function) and
               Code.ensure_loaded?(entry.converter) and function_exported?(entry.converter, entry.converter_function, 2)
           end)

    assert :ok = Registry.validate(entries)
  end

  test "retired codes remain explainable but are excluded from reachable coverage" do
    retired_codes = Enum.map(Registry.retired(), & &1.code)
    assert "E015" in retired_codes
    assert "E018" in retired_codes
    assert length(retired_codes) > 2
    refute Enum.any?(Registry.reachable(), &(&1.code in retired_codes))
    assert {:ok, _} = Cure.Compiler.Errors.explain("E015")
    assert Enum.all?(Registry.retired(), &(is_binary(&1.retirement_reason) and &1.retirement_reason != ""))
    assert Enum.all?(Registry.reachable(), &is_nil(&1.retirement_reason))
    assert Registry.list_all() == Cure.Compiler.Errors.list_all()
    assert Registry.explain("e015") == Cure.Compiler.Errors.explain("E015")
  end

  test "registry validation rejects duplicate ownership and invalid retirement metadata" do
    entry = Enum.find(Registry.entries(), &(&1.status == :reachable))
    code = entry.code

    assert {:error, {:duplicate_code, ^code}} = Registry.validate([entry, entry])

    assert {:error, {:retired_without_reason, ^code}} =
             Registry.validate([%{entry | status: :retired, retirement_reason: nil}])

    assert {:error, {:reachable_with_retirement_reason, ^code}} =
             Registry.validate([%{entry | retirement_reason: "no longer emitted"}])

    assert {:error, {:missing_producer, ^code}} = Registry.validate([%{entry | producers: []}])

    assert {:error, {:missing_converter_function, ^code}} =
             Registry.validate([%{entry | converter_function: :does_not_exist}])

    assert {:error, {:reachable_without_catalog_case, ^code}} =
             Registry.validate([%{entry | catalog_case: nil}])

    assert {:error, {:reachable_without_fixture, ^code}} =
             Registry.validate([%{entry | fixture_id: nil}])
  end

  test "first-party stable diagnostic literals are registered" do
    assert :ok = Registry.validate_sources(Path.wildcard("lib/**/*.ex"))
  end

  test "source validation reports an unregistered stable code" do
    path = Path.join(System.tmp_dir!(), "cure-diagnostic-registry-fixture.ex")
    File.write!(path, ~S(defmodule Fixture do
  @code "E999"
end
))

    on_exit(fn -> File.rm(path) end)

    assert {:error, {:unregistered_source_codes, ["E999"]}} = Registry.validate_sources([path])
  end

  test "E101 is reserved for internal compiler exceptions" do
    entry = Registry.fetch!("e101")
    assert entry.key == :internal_compiler_error
    assert entry.severity == :error
    assert entry.status == :reachable

    try do
      raise ArgumentError, "boom"
    rescue
      exception ->
        diagnostic = Cure.Diagnostic.Operational.internal_exception(exception, __STACKTRACE__)
        assert diagnostic.code == "E101"
        assert diagnostic.payload.fingerprint =~ ~r/^[0-9a-f]{12}$/
        refute Map.has_key?(diagnostic.payload, :stacktrace)
    end

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      Cure.Diagnostic.Adapter.from_error({:ordinary_unhandled_error, :detail})
    end
  end
end
