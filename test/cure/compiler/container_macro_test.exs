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

  test "typed app syntax shares one lifecycle state type" do
    source = "app Cure.TypedApp state Int\n"

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.TypedApp"
    assert apply(module, :start, [:normal, 7]) == {:ok, 7}
    assert apply(module, :stop, [7]) == :ok
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

  test "supervisor child policies reject arbitrary restart atoms" do
    source = """
    mod Main
      use Std.Supervisor
      fn build() -> Std.Supervisor.ChildSpec =
        Std.Supervisor.child_with(:worker_module, :worker, :permanent, Std.Supervisor.shutdown_after(1000), Std.Supervisor.worker())
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
