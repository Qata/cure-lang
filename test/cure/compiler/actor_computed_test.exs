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
  end
end
