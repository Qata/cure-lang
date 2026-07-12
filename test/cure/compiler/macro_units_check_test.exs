defmodule Cure.Compiler.MacroUnitsCheckTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{MacroCheck, MacroUnits}

  test "registers units and elaborates scaled literals" do
    assert {:ok, registry} = MacroUnits.register(%{}, "ms", 1, :duration)
    assert {:ok, registry} = MacroUnits.register(registry, "s", 1_000, :duration)
    assert {:ok, %{scaled: 2_000, unit: %{dimension: :duration}}} = MacroUnits.literal(registry, 2, "s")
    assert {:error, {:unknown_unit, "min"}} = MacroUnits.literal(registry, 1, "min")
  end

  test "property plans are named, typed, and duplicate-free" do
    properties = [%{name: :round_trip, kind: :round_trip, expression: {:call, :round_trip}}]
    assert {:ok, %{kind: :quoted_check_plan, properties: ^properties}} = MacroCheck.plan(:Frame, properties)

    duplicate = properties ++ [%{name: :round_trip, kind: :total, expression: {:call, :total}}]
    assert {:error, :duplicate_check_property} = MacroCheck.plan(:Frame, duplicate)
  end
end
