defmodule Cure.Compiler.FsmComputedTest do
  use ExUnit.Case, async: false

  test "fsm derives its event type and emits the reflected handler" do
    source = """
    mod M
      use Std.Fsm

      fsm Cure.Generated.Derived state Int derive
        match event
          Start -> :keep_state_and_data
          Stop -> :keep_state_and_data

    fn make_start() -> FsmEvent = Start
    fn make_stop() -> FsmEvent = Stop
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(module, :make_start, []) == :Start
    assert apply(module, :make_stop, []) == :Stop

    generated = :"Cure.Generated.Derived"
    assert apply(generated, :handle_event, [:info, :Start, :state, 4]) == :keep_state_and_data
    assert apply(generated, :handle_event, [:info, :Stop, :state, 4]) == :keep_state_and_data
  end

  test "fsm rejects a catch-all event handler" do
    source = """
    mod M
      use Std.Fsm

      fsm Cure.Generated.CatchAll state Int derive
        match event
          event -> :keep_state_and_data
    """

    assert {:error, {:computed_macro_error, _, {:author_failure, "non_constructor_pattern", []}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end
end
