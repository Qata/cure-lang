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
  end

  test "retired codes remain explainable but are excluded from reachable coverage" do
    assert Enum.map(Registry.retired(), & &1.code) == ~w[E015 E018]
    refute Enum.any?(Registry.reachable(), &(&1.code in ~w[E015 E018]))
    assert {:ok, _} = Cure.Compiler.Errors.explain("E015")
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
