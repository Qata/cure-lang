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

  @required_callbacks %{
    GenStatem: [:callback_mode, :init, :handle_event],
    GenServer: [:init],
    Supervisor: [:init],
    Application: [:start, :stop]
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

  @doc "Validate the required portion of one closed OTP behavior contract."
  @spec validate_required_callbacks(atom(), [map()]) :: :ok | {:error, term()}
  def validate_required_callbacks(behaviour, callbacks) when is_list(callbacks) do
    with {:ok, _signatures} <- callback_signatures(behaviour) do
      present = MapSet.new(callbacks, &Map.get(&1, :name))

      case Enum.find(Map.fetch!(@required_callbacks, behaviour), &(not MapSet.member?(present, &1))) do
        nil -> :ok
        missing -> {:error, {:missing_callback, missing, behaviour}}
      end
    end
  end

  @spec lift_module(String.t(), atom(), [map()], [tuple()], keyword()) :: {:ok, map()} | {:error, term()}
  def lift_module(name, behaviour, callbacks, declarations)
      when is_binary(name) and is_list(callbacks) and is_list(declarations) do
    lift_module(name, behaviour, callbacks, declarations, [])
  end

  def lift_module(name, behaviour, callbacks, declarations, opts)
      when is_binary(name) and is_list(callbacks) and is_list(declarations) and is_list(opts) do
    imports = Keyword.get(opts, :imports, imports_from_declarations(declarations))
    source_provenance = Keyword.get(opts, :source_provenance)

    with :ok <- validate_module_name(name),
         :ok <- validate_callbacks(behaviour, callbacks),
         :ok <- validate_required_callbacks(behaviour, callbacks),
         :ok <- validate_declarations(declarations),
         :ok <- validate_imports(imports) do
      {:ok,
       %{
         kind: :quoted_module,
         module: name,
         behaviour: behaviour,
         callbacks: callbacks,
         declarations: declarations,
         imports: imports,
         dependencies: imports,
         source_provenance: source_provenance
       }}
    end
  end

  @doc "Lift a structured module request without compiling or loading it."
  @spec lift_module(map()) :: {:ok, map()} | {:error, term()}
  def lift_module(%{
        module: name,
        behaviour: behaviour,
        callbacks: callbacks,
        declarations: declarations,
        imports: imports,
        source_provenance: source_provenance
      }) do
    lift_module(name, behaviour, callbacks, declarations, imports: imports, source_provenance: source_provenance)
  end

  def lift_module(%{module: name, behaviour: behaviour, callbacks: callbacks, declarations: declarations}) do
    lift_module(name, behaviour, callbacks, declarations)
  end

  @doc "Build a pure supervisor module value from declarative child specs."
  @spec supervisor_module(String.t(), [map()], keyword()) :: {:ok, map()} | {:error, term()}
  def supervisor_module(name, children, opts \\ []) when is_binary(name) and is_list(children) do
    strategy = Keyword.get(opts, :strategy, :one_for_one)
    intensity = Keyword.get(opts, :intensity, 3)
    period = Keyword.get(opts, :period, 5)

    with :ok <- validate_strategy(strategy),
         :ok <- validate_positive(:intensity, intensity),
         :ok <- validate_positive(:period, period),
         :ok <- validate_child_specs(children),
         {:ok, callback} <-
           callback_value(
             :Supervisor,
             :init,
             [{:variable, [scope: :local], "children"}],
             {:supervisor_init, [strategy: strategy, intensity: intensity, period: period], children}
           ),
         {:ok, module} <- lift_module(name, :Supervisor, [callback], []) do
      {:ok, Map.put(module, :container, :supervisor)}
    end
  end

  @doc "Report whether an AtomVM executable is available for the runtime gate."
  @spec atomvm_gate(keyword()) :: :ok | {:error, {:atomvm_unavailable, String.t()}}
  def atomvm_gate(opts \\ []) do
    executable = Keyword.get(opts, :executable, "atomvm")

    case System.find_executable(executable) do
      nil -> {:error, {:atomvm_unavailable, executable}}
      _path -> :ok
    end
  end

  @doc "Validate and lift the parser's pure `lift module` AST node."
  @spec lift_module_ast(tuple()) :: {:ok, map()} | {:error, term()}
  def lift_module_ast({:lift_module, meta, []}) when is_list(meta) do
    with module when is_binary(module) <- Keyword.get(meta, :module),
         behaviour when is_atom(behaviour) <- Keyword.get(meta, :behaviour),
         callbacks when is_list(callbacks) <- Keyword.get(meta, :callbacks, []),
         declarations when is_list(declarations) <- Keyword.get(meta, :declarations, []) do
      opts = [source_provenance: Keyword.get(meta, :source_provenance)]
      opts = if is_list(Keyword.get(meta, :imports)), do: [{:imports, meta[:imports]} | opts], else: opts
      lift_module(module, behaviour, callbacks, declarations, opts)
    else
      _ -> {:error, :invalid_lift_module_ast}
    end
  end

  def lift_module_ast(_other), do: {:error, :invalid_lift_module_ast}

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

  defp validate_imports(imports) do
    if Enum.all?(imports, &is_binary/1), do: :ok, else: {:error, :invalid_lift_import}
  end

  defp imports_from_declarations(declarations) do
    declarations
    |> Enum.flat_map(fn
      {:import, meta, _children} when is_list(meta) -> List.wrap(Keyword.get(meta, :source))
      _ -> []
    end)
    |> Enum.uniq()
  end

  defp validate_strategy(strategy) when strategy in [:one_for_one, :one_for_all, :rest_for_one], do: :ok
  defp validate_strategy(strategy), do: {:error, {:invalid_supervisor_strategy, strategy}}

  defp validate_positive(_name, value) when is_integer(value) and value > 0, do: :ok
  defp validate_positive(name, value), do: {:error, {:invalid_supervisor_option, name, value}}

  defp validate_child_specs(children) do
    ids = Enum.map(children, &Map.get(&1, :id))

    cond do
      not Enum.all?(children, &valid_child_spec?/1) -> {:error, :invalid_supervisor_child}
      length(ids) != MapSet.size(MapSet.new(ids)) -> {:error, :duplicate_supervisor_child}
      true -> :ok
    end
  end

  defp valid_child_spec?(%{id: id, start: start}) when is_atom(id) and is_tuple(start), do: true
  defp valid_child_spec?(_), do: false
end
