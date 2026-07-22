defmodule Cure.Compiler.MacroUnitsCheckTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroCheck, MacroUnits}
  alias Cure.Diagnostic.Renderer

  test "registers units and elaborates scaled literals" do
    assert {:ok, registry} = MacroUnits.register(%{}, "ms", 1, :duration)
    assert {:ok, registry} = MacroUnits.register(registry, "s", 1_000, :duration)
    assert {:ok, %{scaled: 2_000, unit: %{dimension: :duration}}} = MacroUnits.literal(registry, 2, "s")
    assert {:error, {:unknown_unit, "min"}} = MacroUnits.literal(registry, 1, "min")
  end

  test "malformed registry entries are rejected instead of raising" do
    assert {:error, {:invalid_unit, "ms"}} =
             MacroUnits.literal(%{"ms" => %{scale: :fast, dimension: :duration}}, 1, "ms")
  end

  test "every unit validation branch has stable user-facing output" do
    cases = [
      {fn -> MacroUnits.register(%{"ms" => %{scale: 1, dimension: :duration}}, "ms", 1, :duration) end,
       """
       -- UNIT SUFFIX IS ALREADY DECLARED [E092] --------------------------------------

       The `ms` suffix is registered more than once, so a literal would have two
       possible scales.

       Hint: Keep exactly one declaration for the `ms` suffix
       """},
      {fn -> MacroUnits.register(%{}, "ms", 0, :duration) end,
       """
       -- UNIT DECLARATION IS INVALID [E092] ------------------------------------------

       The `ms` unit needs a text suffix, a positive numeric scale, and an atom naming
       its dimension.

       Hint: Use a positive scale and a stable dimension such as `duration`
       """},
      {fn -> MacroUnits.literal(%{}, 1, "min") end,
       """
       -- UNIT SUFFIX IS UNKNOWN [E092] -----------------------------------------------

       The `min` suffix is used by this literal, but no unit with that suffix is
       registered.

       Hint: Register `min` before using it in a literal
       """},
      {fn -> MacroUnits.literal(%{}, :one, "ms") end,
       """
       -- UNIT LITERAL IS MALFORMED [E092] --------------------------------------------

       A unit literal needs a numeric value and a text suffix, but this one uses value
       `one` and suffix `ms`.

       Hint: Use a number followed by a registered text suffix
       """}
    ]

    Enum.each(cases, fn {run, expected} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "units.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_unit_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end

  test "property plans are named, typed, and duplicate-free" do
    properties = [%{name: :round_trip, kind: :round_trip, expression: {:call, :round_trip}}]
    assert {:ok, %{kind: :quoted_check_plan, properties: ^properties}} = MacroCheck.plan(:Frame, properties)

    duplicate = properties ++ [%{name: :round_trip, kind: :total, expression: {:call, :total}}]
    assert {:error, :duplicate_check_property} = MacroCheck.plan(:Frame, duplicate)
  end
end
