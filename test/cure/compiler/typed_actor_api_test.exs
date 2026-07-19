defmodule Cure.Compiler.TypedActorApiTest do
  use ExUnit.Case, async: false

  test "generated actor API starts, folds typed messages, answers requests, and stops" do
    source = """
    mod TypedActorDefinition
      use Std.Actor

      actor Cure.Generated.TypedCounter
        state Int
        on_cast
          Inc -> state + 1
        on_call
          Read -> state

    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.TypedCounter"
    assert {:Started, pid} = apply(actor, :start, [0])

    assert :unit = apply(actor, :send, [pid, :Inc])
    assert :unit = apply(actor, :send, [pid, :Inc])
    assert 2 = apply(actor, :request, [pid, :Read])
    assert :unit = apply(actor, :stop, [pid])
    refute Process.alive?(pid)
  end

  test "generated send rejects values outside the actor message protocol" do
    source = """
    mod WrongTypedActorDefinition
      use Std.Actor

      actor Cure.Generated.TypedCounterNegative
        state Int
        on_cast
          Inc -> state + 1
        body
          fn wrong(handle: Handle) -> Effect(Unit) = send(handle, 42)
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "on_message derives payload-bearing constructors and folds record updates" do
    source = """
    mod PayloadActorDefinition
      use Std.Actor

      rec CounterState
        count: Int
        touched: Bool

      actor Cure.Generated.PayloadCounter
        state CounterState
        initial CounterState{count: 0, touched: false}
        on_message
          Add(amount: Int) -> CounterState{
            state |
            count: state.count + amount,
            touched: true
          }
          Reset() -> CounterState{state | count: 0, touched: false}
    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.PayloadCounter"
    assert {:Started, pid} = apply(actor, :start, [])

    assert :unit = apply(actor, :send, [pid, {:Add, 7}])
    assert :sys.get_state(pid) == {:CounterState, 7, true}
    assert :unit = apply(actor, :send, [pid, :Reset])
    assert :sys.get_state(pid) == {:CounterState, 0, false}
    assert :unit = apply(actor, :stop, [pid])
  end

  test "an explicit reply family gives one actor request-specific reply types" do
    source = """
    mod DependentActorDefinition
      use Std.Actor

      actor Cure.Generated.DependentCounter
        state Int
        initial 3
        on_message
          Increment() -> state + 1
        on_call
          Count() -> CountReply(state)
          Ping() -> Ack()
        reply ReplyOf
        body
          type CountResult = CountReply(Int)
          type AckResult = Ack
          fn ReplyOf(request: ActorRequest) -> Type = match request
            Count() -> CountResult
            Ping() -> AckResult
    """

    assert {:ok, _definition} = Cure.Compiler.compile_and_load(source, emit_events: false)
    actor = :"Cure.Generated.DependentCounter"
    assert {:Started, pid} = apply(actor, :start, [])

    assert {:CountReply, 3} = apply(actor, :request, [pid, :Count])
    assert :Ack = apply(actor, :request, [pid, :Ping])
    assert :unit = apply(actor, :send, [pid, :Increment])
    assert {:CountReply, 4} = apply(actor, :request, [pid, :Count])
    assert :unit = apply(actor, :stop, [pid])
  end

  test "dependent actor queries reject a reply from another request branch" do
    source = """
    mod InvalidDependentActorDefinition
      use Std.Actor

      actor Cure.Generated.InvalidDependentCounter
        state Int
        on_message
          Increment() -> state + 1
        on_call
          Count() -> Ack()
          Ping() -> Ack()
        reply ReplyOf
        body
          type CountResult = CountReply(Int)
          type AckResult = Ack
          fn ReplyOf(request: ActorRequest) -> Type = match request
            Count() -> CountResult
            Ping() -> AckResult
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end
end
