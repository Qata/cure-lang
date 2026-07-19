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

  test "typed FSM states and actions lower to the native gen_statem protocol" do
    source = """
    mod M
      use Std.Fsm

      type DoorState = Locked | Unlocked
      type DoorEvent = Coin | Push

      fsm Cure.Generated.TypedDoor
        state Int
        states DoorState
        initial Locked
        event_type DoorEvent
        events
          Coin -> Next(Unlocked(), data + 1)
          Push -> Keep(data)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert {:ok, pid} = apply(:"Cure.Generated.TypedDoor", :start_link, [0])
    assert :sys.get_state(pid) == {:Locked, 0}

    assert :ok = :gen_statem.cast(pid, :Coin)
    assert :sys.get_state(pid) == {:Unlocked, 1}

    assert :ok = :gen_statem.cast(pid, :Push)
    assert :sys.get_state(pid) == {:Unlocked, 1}
    :gen_statem.stop(pid)
  end

  test "transition-table FSM derives nominal State and Event types from its graph" do
    source = """
    mod M
      use Std.Fsm

      fsm Cure.Generated.Turnstile with Int
        Locked --Coin--> Unlocked
          update data + 1
        Unlocked --Push--> Locked
        Unlocked --Coin--> Unlocked
          update data + 1
        Locked --Push--> Locked
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert {:ok, pid} = apply(:"Cure.Generated.Turnstile", :start_link, [0])
    assert :sys.get_state(pid) == {:Locked, 0}

    assert :ok = :gen_statem.cast(pid, :Coin)
    assert :sys.get_state(pid) == {:Unlocked, 1}

    assert :ok = :gen_statem.cast(pid, :Push)
    assert :sys.get_state(pid) == {:Locked, 1}
    :gen_statem.stop(pid)
  end

  test "transition updates support typed record updates and preserve untouched fields" do
    source = """
    mod M
      use Std.Fsm

      rec TurnstileData
        coins: Int
        pushes: Int
        enabled: Bool

      fsm Cure.Generated.RecordTurnstile with TurnstileData
        Locked --Coin--> Unlocked
          update TurnstileData{data | coins: data.coins + 1}
        Unlocked --Push--> Locked
          update TurnstileData{data | pushes: data.pushes + 1}
        Unlocked --Coin--> Unlocked
          update TurnstileData{data | coins: data.coins + 1}
        Locked --Push--> Locked

      fn initial_data() -> TurnstileData =
        TurnstileData{coins: 0, pushes: 7, enabled: true}
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    initial = apply(module, :initial_data, [])
    assert {:ok, pid} = apply(:"Cure.Generated.RecordTurnstile", :start_link, [initial])
    assert :sys.get_state(pid) == {:Locked, {:TurnstileData, 0, 7, true}}

    assert :ok = :gen_statem.cast(pid, :Coin)
    assert :sys.get_state(pid) == {:Unlocked, {:TurnstileData, 1, 7, true}}

    assert :ok = :gen_statem.cast(pid, :Push)
    assert :sys.get_state(pid) == {:Locked, {:TurnstileData, 1, 8, true}}
    :gen_statem.stop(pid)
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

  test "structured supervisor encodes an explicitly derived child identity" do
    source = """
    mod M
      use Std.Beam
      use Std.Supervisor

      type ChildIdentity = CounterWorker | BackupWorker deriving BeamEncode

      sup Cure.Generated.TypedIdentitySup
        children [child Cure.Generated.Child id CounterWorker()]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"

    assert {:ok, {_strategy, [child]}} =
             apply(:"Cure.Generated.TypedIdentitySup", :init, [[]])

    assert elem(child, 0) == :CounterWorker
    assert elem(elem(child, 1), 0) == :"Cure.Generated.Child"
  end

  test "structured supervisor rejects a child identity without BeamEncode" do
    source = """
    mod M
      use Std.Beam
      use Std.Supervisor

      type ChildIdentity = CounterWorker | BackupWorker

      sup Cure.Generated.UnencodedIdentitySup
        children [child Cure.Generated.Child id CounterWorker()]
    """

    assert {:error, reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert inspect(reason) =~ "macro_capture_obligation_failed"
    assert inspect(reason) =~ "BeamEncode"
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
