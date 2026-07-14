defmodule Cure.Compiler.TransparentObjectMacroTest do
  use ExUnit.Case, async: false

  @containers [
    {"actor", "Cure.TestActor", :start_link, [0]},
    {"fsm", "Cure.TestFsm", :start_link, [0]},
    {"sup", "Cure.TestSup", :start_link, []},
    {"app", "Cure.TestApp", :start, [:normal, []]}
  ]

  test "the four OTP surfaces are auto-preluded syntax macros" do
    for {keyword, name, _fun, _args} <- @containers do
      source = "#{keyword} #{name}\n"
      assert {:ok, ast} = Cure.Compiler.parse_source(source, file: "container_macro.cure")

      case keyword do
        keyword when keyword in ["sup", "actor", "fsm", "app"] ->
          assert {:lift_module, meta, []} = ast
          assert meta[:module] == name

        _ ->
          assert {:container, meta, []} = ast
          assert Keyword.get(meta, :macro_generated)
          assert Keyword.get(meta, :name) == name
      end
    end
  end

  test "a raw container body is parsed by the ordinary parser" do
    assert {:ok, {:lift_module, meta, []}} =
             Cure.Compiler.parse_source("sup Cure.Body\n  strategy = :one_for_all\n", file: "body.cure")

    assert meta[:module] == "Cure.Body"
    assert Enum.any?(meta[:declarations], &match?({:assignment, _, _}, &1))
  end

  test "generic lowering emits runnable OTP modules for every container kind" do
    for {keyword, name, fun, args} <- @containers do
      source = "#{keyword} #{name}\n"
      assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

      expected_module =
        if keyword in ["sup", "actor", "fsm", "app"],
          do: String.to_atom(name),
          else: Module.concat(String.split(name, "."))

      assert module == expected_module
      assert match?({:ok, _}, apply(module, fun, args))
    end
  end

  test "actor payload syntax expands to a zero-argument starter" do
    assert {:ok, module} =
             Cure.Compiler.compile_and_load("actor Cure.PayloadActor with 0\n", emit_events: false)

    assert module == :"Cure.PayloadActor"
    assert match?({:ok, _}, apply(module, :start_link, []))
  end

  test "typed actor syntax shares one state type across callbacks" do
    source = "actor Cure.TypedActor state Int\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.TypedActor"
    assert apply(module, :init, [7]) == {:ok, 7}
    assert apply(module, :handle_cast, [:message, 7]) == {:noreply, 7}
    assert apply(module, :handle_info, [:info, 7]) == {:noreply, 7}
    assert apply(module, :code_change, [:old, 7, :extra]) == {:ok, 7}
  end

  test "typed actor startup passes the scalar state to the OTP init callback" do
    assert {:ok, module} = Cure.Compiler.compile_and_load("actor Cure.ScalarActor state Int\n", emit_events: false)
    assert {:ok, pid} = apply(module, :start_link, [7])
    assert :sys.get_state(pid) == 7
    :gen_server.stop(pid)
  end

  test "typed actor startup permits multiple unnamed instances of one module" do
    assert {:ok, module} =
             Cure.Compiler.compile_and_load("actor Cure.MultiInstanceActor state Int\n", emit_events: false)

    assert {:ok, first} = apply(module, :start_link, [1])
    assert {:ok, second} = apply(module, :start_link, [2])
    assert :sys.get_state(first) == 1
    assert :sys.get_state(second) == 2

    :gen_server.stop(first)
    :gen_server.stop(second)
  end

  test "typed actor state annotations reject mismatched callback bodies" do
    source = """
    macro TypedActor
      syntax typed_actor <name: ModuleName> state <state_type: Type> becomes lift module name
        behaviour gen_server
        typealias State = state_type
        callback init(initial: State) returns Tuple(Atom, State) = %[:ok, true]
    typed_actor Cure.InvalidTypedActor state Int
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor init syntax emits a checked user callback body" do
    source = """
    actor Cure.InitializedActor state Int init
      %[:ok, 7]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :init, [0]) == {:ok, 7}
  end

  test "actor terminate syntax emits a checked lifecycle callback body" do
    source = """
    actor Cure.TerminatingActor state Int terminate
      :shutdown_complete
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :terminate, [:normal, 7]) == :shutdown_complete
  end

  test "actor code_change syntax emits a checked lifecycle callback body" do
    source = """
    actor Cure.CodeChangingActor state Int code_change
      %[:ok, state + 1]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :code_change, [:old, 7, :extra]) == {:ok, 8}
  end

  test "actor lifecycle callback syntax rejects a mismatched state result" do
    source = """
    actor Cure.InvalidCodeChangeActor state Int code_change
      %[:ok, true]
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor handle_info syntax emits a checked user callback body" do
    source = """
    actor Cure.MessageActor state Int handle_info
      %[:noreply, state + 1]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_info, [:tick, 7]) == {:noreply, 8}
  end

  test "actor callback bodies sequence beam operations through an erased effect result" do
    source = """
    actor Cure.EffectActor state Int handle_info
      let pid: Pid(Atom) = beam_ops self
      %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_info, [:tick, 7]) == {:noreply, 7}
  end

  test "actor messages syntax shares an explicit message type with handle_info" do
    source = """
    actor Cure.TypedMessageActor state Int messages Tuple(Atom, Int) handle_info
      let pid: Pid(Tuple(Atom, Int)) = beam_ops self
      %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_info, [[:ping, 1], 7]) == {:noreply, 7}
  end

  test "actor messages syntax rejects an operation typed for another message" do
    source = """
    actor Cure.InvalidMessageActor state Int messages Tuple(Atom, Int) handle_info
      let pid: Pid(Tuple(Atom, Int)) = beam_ops self
      let sent: Effect(Unit) = beam_ops tell pid :wrong
      %[:noreply, state]
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor cast syntax runs a checked transparent message handler" do
    source = """
    actor Cure.CastActor state Int messages Atom handle_cast
      pickup
        message == :inc -> %[:noreply, state + 1]
        else -> %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_cast, [:inc, 4]) == {:noreply, 5}
    assert apply(module, :handle_cast, [:other, 4]) == {:noreply, 4}

    assert {:ok, pid} = apply(module, :start_link, [4])
    :gen_server.cast(pid, :inc)
    assert :sys.get_state(pid) == 5
    :gen_server.stop(pid)
  end

  test "actor cast syntax rejects a body with the wrong state result" do
    source = """
    actor Cure.InvalidCastActor state Int messages Atom handle_cast
      %[:noreply, true]
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "polymorphic actor payload syntax checks a custom cast body" do
    source = """
    actor Cure.PolymorphicCast handle_cast
      %[:noreply, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_cast, [:inc, 4]) == {:noreply, 4}
    assert {:ok, pid} = apply(module, :start_link, [0])
    :gen_server.cast(pid, :inc)
    assert :sys.get_state(pid) == 0
    :gen_server.stop(pid)
  end

  test "actor call syntax keeps request and reply types distinct" do
    source = """
    actor Cure.TypedCallActor state Int call Int returns Bool
      %[:reply, true, state]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_call, [7, :from, 11]) == {:reply, true, 11}
  end

  test "actor call syntax rejects a reply body with the declared wrong type" do
    source = """
    actor Cure.InvalidCallActor state Int call Int returns Bool
      %[:reply, 1, state]
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "actor callback syntax rejects a body with the wrong state result" do
    source = """
    actor Cure.InvalidActor state Int init
      %[:ok, true]
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "fsm payload syntax expands to a zero-argument starter" do
    assert {:ok, module} =
             Cure.Compiler.compile_and_load("fsm Cure.PayloadFsm with 0\n", emit_events: false)

    assert module == :"Cure.PayloadFsm"
    assert match?({:ok, _}, apply(module, :start_link, []))
  end

  test "typed fsm syntax shares one data type across callbacks" do
    source = "fsm Cure.TypedFsm state Int\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.TypedFsm"
    assert apply(module, :callback_mode, []) == :handle_event_function
    assert apply(module, :init, [7]) == {:ok, :initial, 7}
    assert apply(module, :handle_event, [:info, :tick, :red, 7]) == :keep_state_and_data
  end

  test "typed fsm data annotations reject mismatched callback bodies" do
    source = """
    macro TypedFsm
      syntax typed_fsm <name: ModuleName> state <state_type: Type> becomes lift module name
        behaviour gen_statem
        typealias State = state_type
        callback init(initial: State) returns Tuple(Atom, Atom, State) = %[:ok, :initial, true]
    typed_fsm Cure.InvalidTypedFsm state Int
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "fsm init syntax emits a checked user callback body" do
    source = """
    fsm Cure.InitializedFsm state Int init
      %[:ok, :ready, 7]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :init, [0]) == {:ok, :ready, 7}
  end

  test "fsm handle_event syntax emits a checked user callback body" do
    source = """
    fsm Cure.EventFsm state Int handle_event
      :keep_state_and_data
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_event, [:info, :tick, :ready, 7]) == :keep_state_and_data
  end

  test "fsm terminate syntax emits a checked lifecycle callback body" do
    source = """
    fsm Cure.TerminatingFsm state Int terminate
      :shutdown_complete
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :terminate, [:normal, :ready, 7]) == :shutdown_complete
  end

  test "fsm code_change syntax emits a checked lifecycle callback body" do
    source = """
    fsm Cure.CodeChangingFsm state Int code_change
      %[:ok, :ready, data + 1]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :code_change, [:old, :ready, 7, :extra]) == {:ok, :ready, 8}
  end

  test "fsm lifecycle callback syntax rejects a mismatched data result" do
    source = """
    fsm Cure.InvalidCodeChangeFsm state Int code_change
      %[:ok, :ready, true]
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "fsm transition syntax lowers rows and dispatches through ordinary Cure code" do
    source = """
    fsm Cure.TransitionFsm state Int transitions [transition :locked :coin :unlocked, transition :unlocked :push :locked]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :init, [0]) == {:ok, :locked, 0}

    assert apply(module, :handle_event, [:info, :coin, :locked, 0]) ==
             {:next_state, :unlocked, 0}

    assert apply(module, :handle_event, [:info, :push, :unlocked, 0]) ==
             {:next_state, :locked, 0}

    assert apply(module, :handle_event, [:info, :push, :locked, 0]) ==
             {:next_state, :locked, 0}
  end

  test "typed FSM startup passes the scalar state data to the OTP init callback" do
    source = "fsm Cure.ScalarFsm state Int transitions [transition :ready :tick :ready]\n"
    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, pid} = apply(module, :start_link, [9])
    assert :sys.get_state(pid) == {:ready, 9}
    :gen_statem.stop(pid)
  end

  test "fsm callback bodies sequence beam operations through an erased effect result" do
    source = """
    fsm Cure.EffectFsm state Int handle_event
      let pid: Pid(Atom) = beam_ops self
      :keep_state_and_data
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_event, [:info, :tick, :ready, 7]) == :keep_state_and_data
  end

  test "fsm events syntax shares an explicit event type with handle_event" do
    source = """
    fsm Cure.TypedEventFsm state Int events Tuple(Atom, Int) handle_event
      :keep_state_and_data
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_event, [:info, [:ping, 1], :ready, 7]) == :keep_state_and_data
  end

  test "fsm transition syntax preserves an explicit initial state and payload" do
    source = """
    fsm Cure.PayloadTransition state Int initial :locked events Atom transition
      pickup
        event == :coin -> %[:next_state, :unlocked, data + 1]
        else -> %[:next_state, state, data]
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :init, [0]) == {:ok, :locked, 0}

    assert apply(module, :handle_event, [:info, :coin, :locked, 0]) ==
             {:next_state, :unlocked, 1}
  end

  # The `pickup` body is a match, so its motive body is now a direct `{:veffect_type}`
  # — the shape that used to be a spurious `:bad_motive` and forced this callback to
  # launder its result through a `typealias EventResult = Effect(Atom)`. The alias is
  # gone; the callback declares `returns Effect(Atom)` inline.
  test "fsm handle_event pickup bodies check against a direct Effect result type" do
    source = """
    fsm Cure.MatchEventFsm state Int events Atom handle_event
      pickup
        event == :tick -> :keep_state_and_data
        else -> :keep_state_and_data
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :handle_event, [:info, :tick, :ready, 7]) == :keep_state_and_data
  end

  test "fsm callback syntax rejects a body with a non-atom transition result" do
    source = """
    fsm Cure.InvalidEventFsm state Int handle_event
      true
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "typed app syntax shares one lifecycle state type" do
    source = "app Cure.TypedApp state Int\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.TypedApp"
    assert apply(module, :start, [:normal, 7]) == {:ok, 7}
    assert apply(module, :stop, [7]) == :ok
  end

  test "app root syntax emits an ordinary supervisor startup callback" do
    source = "app Cure.RootApp root :root_supervisor\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.RootApp"
    assert function_exported?(module, :start, 2)
  end

  test "app phase syntax emits an ordinary start phase callback" do
    source = """
    app Cure.PhasedApp phase :warm_cache
      :started
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.PhasedApp"
    assert function_exported?(module, :start_phase, 3)
    assert apply(module, :start_phase, [:warm_cache, :normal, []]) == :started
    assert apply(module, :start_phase, [:other_phase, :normal, []]) == :ok
  end

  test "app phases syntax dispatches multiple transparent phase results" do
    source = "app Cure.MultiPhaseApp phases [:warm_cache, :warmed, :ready, :started]\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :start_phase, [:warm_cache, :normal, []]) == :warmed
    assert apply(module, :start_phase, [:ready, :normal, []]) == :started
    assert apply(module, :start_phase, [:other_phase, :normal, []]) == :ok
  end

  test "app root syntax preserves a typed startup payload" do
    source = "app Cure.PayloadRootApp root :root_supervisor with [:boot]\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.PayloadRootApp"
    assert function_exported?(module, :start, 2)
  end

  test "app phase syntax rejects an effectful body with an atom callback result" do
    source = """
    app Cure.ContextualApp phase :warm_cache
      beam_ops self
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "app phase syntax sequences a beam operation before its erased atom result" do
    source = """
    app Cure.EffectfulPhaseApp phase :warm_cache
      let pid: Pid(Atom) = beam_ops self
      :ok
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :start_phase, [:warm_cache, :normal, []]) == :ok
  end

  test "app phase syntax rejects multi-expression phase bodies" do
    source = """
    app Cure.InvalidPhaseApp phase :warm_cache
      :ok
      :ok
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "typed app lifecycle annotations reject mismatched callback bodies" do
    source = """
    macro TypedApp
      syntax typed_app <name: ModuleName> state <state_type: Type> becomes lift module name
        behaviour application
        typealias State = state_type
        callback start(kind: t, args: State) returns Tuple(Atom, State) = %[:ok, true]
    typed_app Cure.InvalidTypedApp state Int
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "nested beam operations are reparsed inside every transparent OTP macro body" do
    for {keyword, name} <- [
          {"actor", "Cure.NestedActor"},
          {"fsm", "Cure.NestedFsm"},
          {"sup", "Cure.NestedSup"},
          {"app", "Cure.NestedApp"}
        ] do
      source = "#{keyword} #{name}\n  fn me() -> Effect(Pid(Atom)) = beam_ops self\n"

      assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert is_pid(apply(module, :me, []))
    end
  end

  test "a concrete Pid goal solves the erased type index of qualified self" do
    source = """
    mod Cure.ConcretePid
      use Std.Otp
      fn me() -> Effect(Pid(Atom)) = Std.Otp.self()
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert is_pid(apply(module, :me, []))
  end

  test "a concrete Pid goal solves the erased type index through beam_ops" do
    source = """
    mod Cure.ConcreteBeamOps
      use Std.Otp
      fn me() -> Effect(Pid(Atom)) = beam_ops self
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert is_pid(apply(module, :me, []))
  end

  test "supervisor payload syntax expands to a zero-argument starter" do
    assert {:ok, module} =
             Cure.Compiler.compile_and_load("sup Cure.PayloadSup with 0\n", emit_events: false)

    assert module == :"Cure.PayloadSup"
    assert match?({:ok, _}, apply(module, :start_link, []))
  end

  test "supervisor child syntax is a typed transparent callback result" do
    source = "sup Cure.ChildRoot children [Std.Supervisor.child(:worker_module, :worker)]\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.ChildRoot"
    assert {:ok, {strategy, children}} = apply(module, :init, [[]])
    assert strategy == {:one_for_one, 3, 5}
    assert [{:worker, {:worker_module, :start_link, []}, :permanent, 5000, :worker, [:worker_module]}] = children
  end

  test "transparent supervisor starts a generated actor child through the common runtime" do
    source = """
    use Std.Supervisor
    actor Cure.SupervisedWorker with 0
    sup Cure.SupervisedRoot children [child_spec Cure.SupervisedWorker :worker]
    """

    assert {:ok, _main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, supervisor} = apply(:"Cure.SupervisedRoot", :start_link, [])
    assert [{:worker, worker, :worker, [:"Cure.SupervisedWorker"]}] = :supervisor.which_children(supervisor)
    assert is_pid(worker)
    assert Process.alive?(worker)
    :supervisor.stop(supervisor)
  end

  test "supervisor child policies are closed typed values" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> ChildSpec =
        Std.Supervisor.child_with(:worker_module, :worker, Std.Supervisor.transient(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build, []) ==
             {:worker, {:worker_module, :start_link, []}, :transient, 1000, :worker, [:worker_module]}
  end

  test "supervisor child startup arguments preserve their checked element type" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> Tuple(Atom, Tuple(Atom, Atom, List(Int)), Atom, Nat, Atom, List(Atom)) =
        Std.Supervisor.child_with_args(:worker_module, :worker, [1], Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build, []) ==
             {:worker, {:worker_module, :start_link, [1]}, :permanent, 1000, :worker, [:worker_module]}
  end

  test "transparent child_spec syntax preserves checked startup arguments" do
    source = "sup Cure.ArgRoot children [child_spec Cure.ArgWorker :worker with [:boot]]\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, {_strategy, [child]}} = apply(module, :init, [[]])

    assert child ==
             {:worker, {:"Cure.ArgWorker", :start_link, [:boot]}, :permanent, 5000, :worker, [:"Cure.ArgWorker"]}
  end

  test "supervisor child startup rejects a heterogeneous argument list" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> ChildSpec =
        Std.Supervisor.child_with_args(:worker_module, :worker, [1, :boot], Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "heterogeneous supervisor arguments require explicit raw-term erasure" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> Tuple(Atom, Tuple(Atom, Atom, List(Std.Otp.RawTerm)), Atom, Nat, Atom, List(Atom)) =
        Std.Supervisor.child_with_raw_args(:worker_module, :worker, [Std.Supervisor.raw_arg(1), Std.Supervisor.raw_arg(:boot)], Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build, []) ==
             {:worker, {:worker_module, :start_link, [1, :boot]}, :permanent, 1000, :worker, [:worker_module]}
  end

  test "raw child_spec syntax requires explicit raw arguments" do
    source = "sup Cure.RawArgRoot children [child_spec Cure.ArgWorker :worker raw with [raw_arg(1), raw_arg(:boot)]]\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, {_strategy, [child]}} = apply(module, :init, [[]])

    assert child ==
             {:worker, {:"Cure.ArgWorker", :start_link, [1, :boot]}, :permanent, 5000, :worker, [:"Cure.ArgWorker"]}
  end

  test "raw child_spec syntax rejects unwrapped heterogeneous arguments" do
    source = "sup Cure.InvalidRawArgRoot children [child_spec Cure.ArgWorker :worker raw with [1, :boot]]\n"

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor child policies reject arbitrary restart atoms" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> Std.Supervisor.ChildSpec =
        Std.Supervisor.child_with(:worker_module, :worker, :permanent, Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor strategies lower from the closed Cure vocabulary" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(Std.Supervisor.one_for_all(), 2, Std.Supervisor.more(9))
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :build, []) == {:one_for_all, 2, 10}
  end

  test "transparent supervisor templates retain lexical imports for bare helpers" do
    assert {:ok, module} = Cure.Compiler.compile_and_load("sup Cure.UnqualifiedSup\n", emit_events: false)
    assert {:ok, {strategy, children}} = apply(module, :init, [[]])
    assert strategy == {:one_for_one, 3, 5}
    assert children == []
  end

  test "supervisor strategy conversion rejects arbitrary atoms" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(:one_for_all, 2, Std.Supervisor.more(9))
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor strategy policies reject negative intensity and period literals" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(Std.Supervisor.one_for_one(), -1, 5)
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor strategy policies reject a zero restart period" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> StrategySpec = Std.Supervisor.supervision_strategy(Std.Supervisor.one_for_one(), 0, 0)
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor shutdown policies reject unrestricted integer variables" do
    source = """
    mod Main
      use Std.Supervisor
      fn build(timeout: Int) -> ChildSpec =
        Std.Supervisor.child_with(:worker_module, :worker, Std.Supervisor.permanent(), Std.Supervisor.shutdown_after(timeout), Std.Supervisor.worker())
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "supervisor child constructors reject non-atom modules" do
    source = "sup Cure.InvalidChildRoot children [Std.Supervisor.child(1, :worker)]\n"

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "no per-container compiler modules remain in the lowering path" do
    refute Code.ensure_loaded?(Cure.Actor.Compiler)
    refute Code.ensure_loaded?(Cure.FSM.Compiler)
    refute Code.ensure_loaded?(Cure.Sup.Compiler)
    refute Code.ensure_loaded?(Cure.App.Compiler)
  end
end
