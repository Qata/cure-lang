defmodule Cure.Compiler.MacroPacketTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroPacket

  test "builds a dependency-ordered packet layout and property plan" do
    fields = [
      %{name: :version, kind: :scalar, type: :byte},
      %{name: :length, kind: :scalar, type: :byte},
      %{name: :payload, kind: :bytes, length: :length},
      %{name: :crc, kind: :crc, over: [:version, :length, :payload]}
    ]

    assert {:ok, packet} = MacroPacket.build(:Frame, fields, endian: :be)
    assert packet.kind == :quoted_packet
    assert packet.properties == [:round_trip, :total_parse, :fault_rejection]
    assert {:packet_def, [name: :Frame, endian: :be], ^fields} = hd(packet.declarations)
    assert Enum.at(packet.layout, 2) == {:payload, 2, nil}
  end

  test "rejects forward dependencies, missing endianness, and duplicate fields" do
    assert {:error, {:forward_packet_length, :payload, :length}} =
             MacroPacket.build(:Frame, [%{name: :payload, kind: :bytes, length: :length}])

    assert {:error, {:missing_packet_endian, :value}} =
             MacroPacket.build(:Frame, [%{name: :value, kind: :scalar, type: :u16}])

    assert {:error, :duplicate_packet_field} =
             MacroPacket.build(:Frame, [%{name: :x, kind: :scalar, type: :byte}, %{name: :x, kind: :scalar, type: :byte}])
  end

  test "crc coverage names undeclared fields" do
    assert {:error, {:invalid_packet_crc_fields, :crc, [:missing]}} =
             MacroPacket.build(:Frame, [
               %{name: :value, kind: :scalar, type: :byte},
               %{name: :crc, kind: :crc, over: [:value, :missing]}
             ])
  end
end
