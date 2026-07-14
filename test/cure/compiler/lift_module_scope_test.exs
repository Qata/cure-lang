defmodule Cure.Compiler.LiftModuleScopeTest do
  use ExUnit.Case, async: false

  # A lifted module is generated INSIDE a compilation unit, so it sees that
  # unit's scope. Without this an `actor` is hermetically sealed from its own
  # file: it can only speak in structural types (`Atom`, `Tuple(Atom, Int)`) and
  # can never name a message type the program actually declares.
  #
  # `compile_and_load/2` loads every unit but returns the MAIN module, so these
  # address the generated module by name.

  defp lifted!(source, module) do
    assert {:ok, _main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    module
  end

  test "a lifted module accepts a message type declared by the enclosing unit" do
    source = """
    type Cmd = Inc | Dec

    actor Cure.InheritedMessageActor state Int messages Cmd handle_cast
      match message
        Inc -> %[:noreply, state + 1]
        Dec -> %[:noreply, state - 1]
    """

    module = lifted!(source, :"Cure.InheritedMessageActor")
    assert apply(module, :handle_cast, [:Inc, 4]) == {:noreply, 5}
    assert apply(module, :handle_cast, [:Dec, 4]) == {:noreply, 3}
  end

  test "a lifted module accepts a state type declared by the enclosing unit" do
    source = """
    type Light = Red | Green

    actor Cure.InheritedStateActor state Light messages Atom handle_cast
      %[:noreply, state]
    """

    module = lifted!(source, :"Cure.InheritedStateActor")
    assert apply(module, :handle_cast, [:go, :Red]) == {:noreply, :Red}
  end

  test "a lifted module accepts a type alias declared by the enclosing unit" do
    source = """
    typealias Tick = Atom

    actor Cure.InheritedAliasActor state Int messages Tick handle_cast
      %[:noreply, state]
    """

    module = lifted!(source, :"Cure.InheritedAliasActor")
    assert apply(module, :handle_cast, [:tick, 1]) == {:noreply, 1}
  end

  test "a callback body calls a function declared by the enclosing unit" do
    source = """
    fn bump(n: Int) -> Int = n + 1

    actor Cure.InheritedFunctionActor state Int messages Atom handle_cast
      %[:noreply, bump(state)]
    """

    module = lifted!(source, :"Cure.InheritedFunctionActor")
    assert apply(module, :handle_cast, [:go, 4]) == {:noreply, 5}
  end

  test "a lifted module keeps its own definition when the enclosing unit shares a name" do
    source = """
    typealias State = Bool

    actor Cure.ShadowedStateActor state Int messages Atom handle_cast
      %[:noreply, state + 1]
    """

    module = lifted!(source, :"Cure.ShadowedStateActor")
    assert apply(module, :handle_cast, [:go, 4]) == {:noreply, 5}
  end

  test "an inherited message type is still checked against the handler" do
    source = """
    type Cmd = Inc | Dec

    actor Cure.InheritedRejectActor state Int messages Cmd handle_cast
      let sent: Effect(Unit) = beam_ops tell beam_ops self :not_a_cmd
      %[:noreply, state]
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end
end
