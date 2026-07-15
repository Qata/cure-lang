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

  test "structured fsm accepts an explicit event type override" do
    source = """
    mod M
      use Std.Fsm

      type EventKind = Tick | Stop

      fsm Cure.Generated.ExplicitEvents
        state Int
        event_type EventKind
        events
          Tick -> :keep_state_and_data
          Stop -> :keep_state_and_data

    fn make_event() -> EventKind = Tick
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(module, :make_event, []) == :Tick
    assert apply(:"Cure.Generated.ExplicitEvents", :handle_event, [:cast, :Tick, :initial, 0]) == :keep_state_and_data
    assert apply(:"Cure.Generated.ExplicitEvents", :handle_event, [:cast, :Stop, :initial, 3]) == :keep_state_and_data
  end

  test "supervisor accepts the reusable structured family surface" do
    source = """
    mod M
      use Std.Supervisor

      sup Cure.Generated.StructuredSup
        children []
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.Generated.StructuredSup", :init, [[]]) == {:ok, {{:one_for_one, 3, 5}, []}}
  end

  test "structured supervisor recursively expands nested child syntax" do
    source = """
    mod M
      use Std.Supervisor

      sup Cure.Generated.NestedSup
        children [child_spec Cure.Generated.Child :worker]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"

    assert {:ok, {{:one_for_one, 3, 5}, [child]}} =
             apply(:"Cure.Generated.NestedSup", :init, [[]])

    assert child ==
             {:worker, {:"Cure.Generated.Child", :start_link, []}, :permanent, 5000, :worker, [:"Cure.Generated.Child"]}
  end

  test "application accepts the reusable structured family surface" do
    source = """
    mod M
      use Std.App

      app Cure.Generated.StructuredApp
        root Cure.Generated.StructuredSup
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.Generated.StructuredApp", :stop, [:state]) == :ok
    assert apply(:"Cure.Generated.StructuredApp", :start_phase, [:boot, :normal, []]) == :ok
  end
end
