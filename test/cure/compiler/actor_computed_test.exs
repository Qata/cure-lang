defmodule Cure.Compiler.ActorComputedTest do
  use ExUnit.Case, async: false

  test "actor can be produced by a source-defined computed declaration" do
    source = """
    mod M
      use Std.Actor
      use Std.Otp

      actor Cure.Generated.Derived state Int derive
        match message
          Inc -> 1

    fn make_message() -> ActorMessage = Inc
      fn keep_message(message: ActorMessage) -> ActorMessage = message
      fn send_inc() -> Effect(Unit) =
        let pid: Pid(ActorMessage) = beam_ops self
        let sent: Effect(Unit) = beam_ops tell pid Inc
        sent
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert Code.ensure_loaded?(:"Cure.Generated.Derived")
    assert apply(module, :make_message, []) == :Inc
    assert function_exported?(module, :send_inc, 0)
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

  test "computed actor handlers retain enclosing declarations without importing macro scope" do
    source = """
    mod M
      use Std.Actor

      fn bump(value: Int) -> Int = value + 1

      actor Cure.Generated.Enclosing state Int derive
        match message
          Inc -> bump(state)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.Generated.Enclosing", :handle_cast, [:Inc, 4]) == {:noreply, 5}
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

  test "actor derives a typed payload constructor from a typed handler pattern" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.Payload state Int derive
        match message
          Ping(value: Int) -> value

    fn make_message() -> ActorMessage = Ping(7)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :make_message, []) == {:Ping, 7}
    assert apply(:"Cure.Generated.Payload", :handle_cast, [{:Ping, 7}, 0]) == {:noreply, 7}
  end

  test "actor derives a typed request and reply callback from an optional call arm" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.Call state Int derive
        match message
          Ping -> 1
        call
          match request
            Get -> state
            Pong -> state

    fn make_request() -> ActorRequest = Get
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(module, :make_request, []) == :Get

    assert {:ok, pid} = apply(:"Cure.Generated.Call", :start_link, [7])
    assert :gen_server.call(pid, :Get) == 7
    assert :gen_server.call(pid, :Pong) == 7
    :gen_server.stop(pid)
  end

  test "actor derives one reply type across an arbitrary number of call arms" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.ManyCall state Int derive
        match message
          Ping -> 1
        call
          match request
            Get -> state
            Pong -> state
            Count -> state

    fn make_request() -> ActorRequest = Count
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(module, :make_request, []) == :Count

    assert {:ok, pid} = apply(:"Cure.Generated.ManyCall", :start_link, [12])
    assert :gen_server.call(pid, :Count) == 12
    :gen_server.stop(pid)
  end

  test "actor rejects inconsistent reply categories across call arms" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.InconsistentCall state Int derive
        match message
          Ping -> 1
        call
          match request
            Get -> state
            Count -> state
            Reset -> 1
    """

    assert {:error, {:computed_macro_error, _, {:author_failure, "inconsistent_reply_types", []}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor rejects a call reply whose type cannot be inferred" do
    source = """
    mod M
      use Std.Actor

      fn reply(state: Int) -> Int = state

      actor Cure.Generated.InvalidCall state Int derive
        match message
          Ping -> 1
        call
          match request
            Get -> reply(state)
    """

    assert {:error, {:computed_macro_error, _, {:author_failure, "reply_type_not_derivable", []}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor still rejects an untyped payload constructor" do
    source = """
    mod M
      use Std.Actor

      actor Cure.Generated.UntypedPayload state Int derive
        match message
          Ping(value) -> value
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
