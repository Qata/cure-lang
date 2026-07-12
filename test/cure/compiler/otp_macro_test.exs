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

  test "callback constructors are closed and callback values retain quoted bodies" do
    assert {:ok, constructors} = OtpMacro.callback_constructors(:GenServer)
    assert %{name: :handle_call, arity: 3, constructor: :HandleCall} in constructors

    assert {:ok, callback} = OtpMacro.callback_value(:GenServer, :init, [:arg], {:literal, [], 0})
    assert callback.constructor == :Init
    assert callback.body == {:literal, [], 0}

    assert {:error, {:callback_arity, :init, 2, 1}} =
             OtpMacro.callback_value(:GenServer, :init, [:a, :b], :body)
  end

  test "module lifting rejects non-module names and non-quoted declarations" do
    assert {:error, {:invalid_module_name, "Generated"}} =
             OtpMacro.lift_module("Generated", :Supervisor, [], [])

    assert {:error, :invalid_lift_declaration} =
             OtpMacro.lift_module("Cure.Generated.Supervisor", :Supervisor, [], [:not_a_declaration])
  end
end
