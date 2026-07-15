defmodule Cure.Compiler.ActorComputedTest do
  use ExUnit.Case, async: false

  test "actor can be produced by a source-defined computed declaration" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.Derived state Int derive
        match message
          Inc -> 1

    fn make_message() -> ActorMessage = Inc
      fn keep_message(message: ActorMessage) -> ActorMessage = message
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert Code.ensure_loaded?(:"Cure.Generated.Derived")
    assert apply(module, :make_message, []) == :Inc
    assert apply(:"Cure.Generated.Derived", :init, [0]) == {:ok, 0}
    assert apply(:"Cure.Generated.Derived", :handle_cast, [:Inc, 0]) == {:noreply, 0}
    assert apply(:"Cure.Generated.Derived", :handle_info, [:Inc, 0]) == {:noreply, 0}
  end

  test "actor derives its message type from multiple reflected handler arms" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.Handler state Int derive
        match message
          Inc -> 1
          Stop -> 2

    fn make_inc() -> ActorMessage = Inc
    fn make_stop() -> ActorMessage = Stop
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(module, :make_inc, []) == :Inc
    assert apply(module, :make_stop, []) == :Stop
    assert apply(:"Cure.Generated.Handler", :handle_cast, [:Inc, 4]) == {:noreply, 4}
    assert apply(:"Cure.Generated.Handler", :handle_cast, [:Stop, 4]) == {:noreply, 4}
  end
end
