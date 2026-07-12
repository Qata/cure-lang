defmodule Cure.Compiler.OtpMacro do
  @moduledoc """
  Closed OTP callback vocabulary and pure module-value minting.

  This is frontend data validation only. It deliberately never compiles or
  loads a BEAM module; a later orchestrator may consume the returned value.
  """

  @callbacks %{
    GenStatem: %{callback_mode: 0, init: 1, handle_event: 4},
    GenServer: %{init: 1, handle_call: 3, handle_cast: 2, handle_info: 2, terminate: 2, code_change: 3},
    Supervisor: %{init: 1},
    Application: %{start: 2, stop: 1, start_phase: 3}
  }

  @spec callback_signatures(atom()) :: {:ok, map()} | {:error, {:unknown_behaviour, atom()}}
  def callback_signatures(behaviour) do
    case Map.fetch(@callbacks, behaviour) do
      {:ok, signatures} -> {:ok, signatures}
      :error -> {:error, {:unknown_behaviour, behaviour}}
    end
  end

  @spec validate_callbacks(atom(), [map()]) :: :ok | {:error, term()}
  def validate_callbacks(behaviour, callbacks) when is_list(callbacks) do
    with {:ok, signatures} <- callback_signatures(behaviour) do
      Enum.reduce_while(callbacks, :ok, fn %{name: name, arity: arity}, :ok ->
        case Map.fetch(signatures, name) do
          :error -> {:halt, {:error, {:unknown_callback, name, behaviour}}}
          {:ok, ^arity} -> {:cont, :ok}
          {:ok, expected} -> {:halt, {:error, {:callback_arity, name, arity, expected}}}
        end
      end)
    end
  end

  @spec lift_module(String.t(), atom(), [map()], [tuple()]) :: {:ok, map()} | {:error, term()}
  def lift_module(name, behaviour, callbacks, declarations)
      when is_binary(name) and is_list(callbacks) and is_list(declarations) do
    with :ok <- validate_callbacks(behaviour, callbacks) do
      {:ok, %{module: name, behaviour: behaviour, callbacks: callbacks, declarations: declarations}}
    end
  end
end
