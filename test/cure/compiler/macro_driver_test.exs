defmodule Cure.Compiler.MacroDriverTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroDriver

  @registers [
    %{name: :status, offset: 0, width: 8, access: :read},
    %{name: :control, offset: 2, width: 16, access: :read_write}
  ]

  test "builds a pure register-map declaration" do
    assert {:ok, driver} = MacroDriver.build(:Sensor, @registers, base: 0x4000)
    registers = @registers
    assert driver.kind == :quoted_driver
    assert driver.base == 0x4000
    assert {:driver_def, [name: :Sensor], ^registers} = hd(driver.declarations)
  end

  test "rejects duplicate and overlapping register ranges" do
    duplicate = [%{name: :status, offset: 0, width: 8, access: :read}, %{name: :status, offset: 2, width: 8, access: :write}]
    assert {:error, :duplicate_driver_register} = MacroDriver.build(:Sensor, duplicate)

    overlap = [%{name: :a, offset: 0, width: 16, access: :read}, %{name: :b, offset: 1, width: 8, access: :read}]
    assert {:error, :overlapping_driver_register} = MacroDriver.build(:Sensor, overlap)
  end
end
