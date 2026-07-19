defmodule Cure.Elab.BeamEncodeTest do
  use ExUnit.Case, async: true

  test "an ADT can derive its native BEAM representation" do
    source = """
    mod Cure.BeamDerived
      use Std.Beam

      type Message = Ping | Data(Int) deriving BeamEncode

      fn encode(message: Message) -> BeamTerm = to_beam(message)
      fn ping() -> BeamTerm = encode(Ping())
      fn data(value: Int) -> BeamTerm = encode(Data(value))
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :ping, []) == :Ping
    assert apply(module, :data, [7]) == {:Data, 7}
  end

  test "a hand-written BeamEncode implementation overrides the derived representation" do
    source = """
    mod Cure.BeamOverride
      use Std.Beam

      type Message = Ping | Data(Int)

      implementation BeamEncode for Message
        fn to_beam(message: Message) -> BeamTerm = forget(:wire_message)

      fn encode(message: Message) -> BeamTerm = to_beam(message)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :encode, [:Ping]) == :wire_message
    assert apply(module, :encode, [{:Data, 7}]) == :wire_message
  end

  test "BeamDecode is not fabricated for foreign input" do
    source = """
    mod Cure.NoBeamDecoder
      use Std.Beam

      type Message = Ping

      fn decode(term: BeamTerm) -> Result(BeamDecodeError, Message) = from_beam(term)
    """

    assert {:error, {:no_instance, :BeamDecode, _type}} = Cure.Elab.Program.elaborate(source)
  end
end
