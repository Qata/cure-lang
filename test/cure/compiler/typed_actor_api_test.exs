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
end
