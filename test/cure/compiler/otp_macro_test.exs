defmodule Cure.Compiler.OtpMacroTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.OtpMacro

  test "valid supervisor callbacks mint a pure module value" do
    callbacks = [%{name: :init, arity: 1}]
    declarations = [{:function_def, [name: "init"], []}]

    assert {:ok, module_value} =
             OtpMacro.lift_module("Cure.Generated.Supervisor", :Supervisor, callbacks, declarations)

    assert module_value.module == "Cure.Generated.Supervisor"
    assert module_value.behaviour == :Supervisor
    assert module_value.callbacks == callbacks
    assert module_value.declarations == declarations
  end

  test "callback vocabulary rejects unknown names and wrong arities" do
    assert {:error, {:unknown_callback, :handle_call, :Supervisor}} =
             OtpMacro.validate_callbacks(:Supervisor, [%{name: :handle_call, arity: 3}])

    assert {:error, {:callback_arity, :init, 2, 1}} =
             OtpMacro.validate_callbacks(:GenServer, [%{name: :init, arity: 2}])

    assert {:error, {:unknown_behaviour, :Other}} = OtpMacro.validate_callbacks(:Other, [])
  end
end
