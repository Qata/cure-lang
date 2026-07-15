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
    assert apply(:"Cure.Generated.Derived", :handle_cast, [:Inc, 0]) == {:noreply, 1}
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
    assert apply(:"Cure.Generated.Handler", :handle_cast, [:Inc, 4]) == {:noreply, 1}
    assert apply(:"Cure.Generated.Handler", :handle_cast, [:Stop, 4]) == {:noreply, 2}
  end

  test "actor rejects duplicate handler arms after deriving the message type" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.Dedup state Int derive
        match message
          Inc -> 1
          Inc -> 2

    fn make_message() -> ActorMessage = Inc
    """

    assert {:error, {:lift_module_error, _, {:duplicate_branch, _}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor rejects payload constructors without a payload type view" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.Payload state Int derive
        match message
          Ping(value) -> value

    fn make_message() -> ActorMessage = Ping(7)
    """

    assert {:error, {:computed_macro_error, _, {:author_failure, "payload_type_not_derivable", []}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor rejects guarded handler heads with a macro diagnostic" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.Guarded state Int derive
        match message
          Inc when true -> 1
    """

    assert {:error, {:computed_macro_error, _, {:author_failure, "guarded_handler", []}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor rejects variable catch-all handler heads" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.CatchAll state Int derive
        match message
          message -> 1
    """

    assert {:error, {:computed_macro_error, _, {:author_failure, "non_constructor_pattern", []}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end
end
