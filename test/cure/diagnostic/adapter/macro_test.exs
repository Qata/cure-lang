defmodule Cure.Diagnostic.Adapter.MacroTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Adapter
  alias Cure.Diagnostic.Adapter.Macro, as: MacroAdapter
  alias Cure.Diagnostic.Renderer
  alias Cure.Diagnostic.SourceRegistry

  test "syntax-family fields and captures retain authored repairs" do
    source = "stte payload other\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:macro, source, "macro.cure")

    {:ok, field} = SourceRegistry.span(registry, :macro, 0, 4)
    {:ok, capture} = SourceRegistry.span(registry, :macro, 5, 12)
    {:ok, first} = SourceRegistry.span(registry, :macro, 13, 18)

    errors = [
      {:unknown_syntax_family_field,
       %{
         family: "Definition",
         field: "stte",
         valid_fields: ["state", "events"],
         span: field
       }},
      {:missing_syntax_family_field, %{family: "Definition", field: "state", span: field}},
      {:unknown_macro_obligation_capture,
       %{
         interface: "Show",
         capture: "payload",
         available_captures: ["paylod", "state"],
         span: capture
       }},
      {:unit_type_reserved, %{name: "Duration", span: field, unit_span: first}},
      {:duplicate_syntax_family_field, %{field: "state", span: field, first_span: first}}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.primary
      assert direct.suggestions != []
    end

    typo = MacroAdapter.from_error(hd(errors))

    assert [
             %{
               applicability: :machine_applicable,
               edits: [%{span: ^field, replacement: "state"}]
             }
           ] = typo.suggestions

    rendered = Renderer.plain(typo, registry, width: 80)
    assert rendered =~ "UNKNOWN SYNTAX-FAMILY FIELD [E092]"
    assert rendered =~ "^^^^ this field is not declared by the family"
    assert rendered =~ "Hint: Replace it with `state`"
  end

  test "unowned errors are rejected by the macro family boundary" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      MacroAdapter.from_error({:unknown_macro_producer, %{}})
    end
  end

  test "packet validation producers are owned by the macro family" do
    errors = [
      {:invalid_packet_name, :Frame},
      {:invalid_packet_endian, :middle},
      {:unknown_packet_scalar, :u128},
      {:missing_packet_endian, :length},
      {:invalid_packet_field, :bad},
      {:forward_packet_length, :payload, :length},
      {:invalid_packet_crc_fields, :checksum, [:payload]},
      :invalid_packet_field_name,
      :duplicate_packet_field
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_packet_validation
      assert direct.suggestions != []
    end
  end

  test "driver validation producers are owned by the macro family" do
    errors = [
      {:invalid_driver_base, -1},
      :invalid_driver_register,
      :duplicate_driver_register,
      :overlapping_driver_register
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_driver_validation
      assert direct.suggestions != []
    end
  end

  test "board validation producers are owned by the macro family" do
    errors = [
      {:invalid_board_name, :Board},
      {:invalid_board_chip, :chip},
      {:unknown_board_pin, 99},
      {:invalid_board_capability, 8},
      {:invalid_board_bus, :i2c},
      {:unknown_bus_pin, :i2c},
      {:missing_bus_capability, :i2c},
      :invalid_board_definition,
      :missing_board_chip,
      :invalid_board_pins,
      :invalid_board_capabilities,
      :invalid_board_buses,
      :invalid_board_flash,
      :flash_offset_out_of_bounds
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_board_validation
      assert direct.suggestions != []
    end
  end

  test "expansion failures blame authored invocation frames" do
    source = "outer inner\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:expansion, source, "expansion.cure")

    {:ok, outer} = SourceRegistry.span(registry, :expansion, 0, 5)
    {:ok, inner} = SourceRegistry.span(registry, :expansion, 6, 11)

    frames = [
      %{keyword: "outer", invocation: outer},
      %{keyword: "inner", invocation: inner, parent: outer}
    ]

    errors = [
      {:macro_expansion_cycle, frames},
      {:macro_expansion_budget, :expansion_count, frames},
      {:expansion_ill_typed, %{keyword: "inner", input: :input, expansion: :output, reason: :bad}}
    ]

    for error <- errors do
      opts = [span: inner]
      direct = MacroAdapter.from_error(error, opts)
      assert Adapter.from_error(error, opts) == direct
      assert direct.code == "E092"
      assert direct.primary.span == inner
    end

    cycle = MacroAdapter.from_error(hd(errors))
    assert hd(cycle.secondary).span == outer
    assert Enum.map(cycle.provenance, & &1.name) == ["outer", "inner"]
    assert cycle.suggestions != []

    rendered = Renderer.plain(cycle, registry, width: 80)
    assert rendered =~ "MACRO EXPANSION CYCLE [E092]"
    assert rendered =~ "this invocation closes the expansion cycle"
    assert rendered =~ "Hint: Make recursive macro expansion consume input"
  end
end
