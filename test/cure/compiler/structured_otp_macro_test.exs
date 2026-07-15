defmodule Cure.Compiler.StructuredOtpMacroTest do
  use ExUnit.Case, async: false

  test "fsm accepts the reusable structured family surface" do
    source = """
    mod M
      use Std.Fsm

      fsm Cure.Generated.StructuredFsm
        state Int
        events
          Tick -> :keep_state_and_data

    fn make_event() -> FsmEvent = Tick
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(module, :make_event, []) == :Tick
    assert apply(:"Cure.Generated.StructuredFsm", :init, [0]) == {:ok, :initial, 0}

    assert apply(:"Cure.Generated.StructuredFsm", :handle_event, [
             :cast,
             :Tick,
             :initial,
             0
           ]) == :keep_state_and_data
  end
end
