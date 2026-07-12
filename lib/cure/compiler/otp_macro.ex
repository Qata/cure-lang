defmodule Cure.Compiler.OtpMacro do
  @moduledoc """
  Closed OTP callback vocabulary and pure module-value minting.

  This is frontend data validation only. It deliberately never compiles or
  loads a BEAM module; a later orchestrator may consume the returned value.
  """

  @callbacks %{
    GenStatem: %{
      callback_mode: %{arity: 0, constructor: :CallbackMode},
      init: %{arity: 1, constructor: :Init},
      handle_event: %{arity: 4, constructor: :HandleEvent}
    },
    GenServer: %{
      init: %{arity: 1, constructor: :Init},
      handle_call: %{arity: 3, constructor: :HandleCall},
      handle_cast: %{arity: 2, constructor: :HandleCast},
      handle_info: %{arity: 2, constructor: :HandleInfo},
      terminate: %{arity: 2, constructor: :Terminate},
      code_change: %{arity: 3, constructor: :CodeChange}
    },
    Supervisor: %{init: %{arity: 1, constructor: :Init}},
    Application: %{
      start: %{arity: 2, constructor: :Start},
      stop: %{arity: 1, constructor: :Stop},
      start_phase: %{arity: 3, constructor: :StartPhase}
    }
  }

  @type callback :: %{
          name: atom(),
          arity: non_neg_integer(),
          constructor: atom(),
          body: term()
        }

  @doc "Return the closed OTP behaviour vocabulary."
  @spec behaviours() :: [atom()]
  def behaviours, do: Map.keys(@callbacks)

  @spec callback_signatures(atom()) :: {:ok, map()} | {:error, {:unknown_behaviour, atom()}}
  def callback_signatures(behaviour) do
    case Map.fetch(@callbacks, behaviour) do
      {:ok, signatures} -> {:ok, Map.new(signatures, fn {name, %{arity: arity}} -> {name, arity} end)}
      :error -> {:error, {:unknown_behaviour, behaviour}}
    end
  end

  @doc "Return the closed callback constructors for one OTP behaviour."
  @spec callback_constructors(atom()) :: {:ok, [map()]} | {:error, {:unknown_behaviour, atom()}}
  def callback_constructors(behaviour) do
    case Map.fetch(@callbacks, behaviour) do
      {:ok, signatures} ->
        {:ok,
         Enum.map(signatures, fn {name, %{arity: arity, constructor: constructor}} ->
           %{name: name, arity: arity, constructor: constructor}
         end)}

      :error ->
        {:error, {:unknown_behaviour, behaviour}}
    end
  end

  @doc "Build one closed callback value after validating its OTP constructor."
  @spec callback_value(atom(), atom(), [term()], term()) :: {:ok, callback()} | {:error, term()}
  def callback_value(behaviour, name, args, body) when is_atom(name) and is_list(args) do
    with {:ok, signatures} <- callback_constructors(behaviour),
         {:ok, %{arity: arity, constructor: constructor}} <- fetch_callback(signatures, name),
         :ok <- validate_arity(name, length(args), arity) do
      {:ok, %{name: name, arity: arity, constructor: constructor, args: args, body: body}}
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
    with :ok <- validate_module_name(name),
         :ok <- validate_callbacks(behaviour, callbacks),
         :ok <- validate_declarations(declarations) do
      {:ok,
       %{
         kind: :quoted_module,
         module: name,
         behaviour: behaviour,
         callbacks: callbacks,
         declarations: declarations
       }}
    end
  end

  @doc "Lift a structured module request without compiling or loading it."
  @spec lift_module(map()) :: {:ok, map()} | {:error, term()}
  def lift_module(%{module: name, behaviour: behaviour, callbacks: callbacks, declarations: declarations}) do
    lift_module(name, behaviour, callbacks, declarations)
  end

  defp fetch_callback(signatures, name) do
    case Enum.find(signatures, &(&1.name == name)) do
      nil -> {:error, {:unknown_callback, name}}
      signature -> {:ok, signature}
    end
  end

  defp validate_arity(_name, actual, expected) when actual == expected, do: :ok
  defp validate_arity(name, actual, expected), do: {:error, {:callback_arity, name, actual, expected}}

  defp validate_module_name(name) do
    if Regex.match?(~r/^Cure\.[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*$/, name),
      do: :ok,
      else: {:error, {:invalid_module_name, name}}
  end

  defp validate_declarations(declarations) do
    if Enum.all?(declarations, &is_tuple/1), do: :ok, else: {:error, :invalid_lift_declaration}
  end
end
