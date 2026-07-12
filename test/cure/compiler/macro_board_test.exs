defmodule Cure.Compiler.MacroBoardTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroBoard

  @definition %{
    chip: :esp32c3,
    pins: {0, 21},
    capabilities: %{8 => [:input, :output], 9 => [:input, :output, :strapping]},
    buses: %{i2c0: %{sda: 8, scl: 9}},
    flash: %{size: 4_000_000, app_offset: 2_400_000, libs_offset: 1_900_000}
  }

  test "builds a board manifest with checked pins, buses, and flash map" do
    assert {:ok, board} = MacroBoard.build(:Esp32c3, @definition)
    assert board.kind == :quoted_board
    assert MapSet.member?(board.pins, 21)
    assert board.buses.i2c0.sda == 8
  end

  test "rejects unknown pins, missing bus capability declarations, and bad flash bounds" do
    assert {:error, {:unknown_board_pin, 22}} =
             MacroBoard.build(:Esp32c3, put_in(@definition.capabilities[22], [:input]))

    bad_bus = put_in(@definition.buses.i2c0.sda, 7)
    assert {:error, {:missing_bus_capability, :i2c0}} = MacroBoard.build(:Esp32c3, bad_bus)

    bad_flash = put_in(@definition.flash.app_offset, 4_000_000)
    assert {:error, :flash_offset_out_of_bounds} = MacroBoard.build(:Esp32c3, bad_flash)
  end
end
