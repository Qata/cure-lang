defmodule Cure.Diagnostic.Registry.Entry do
  @moduledoc false

  @enforce_keys [
    :code,
    :key,
    :severity,
    :title,
    :status,
    :subsystem,
    :payload_schema,
    :converter,
    :catalog_case,
    :explanation
  ]
  defstruct @enforce_keys

  @type t :: %__MODULE__{
          code: String.t(),
          key: atom(),
          severity: Cure.Diagnostic.severity(),
          title: String.t(),
          status: :reachable | :retired,
          subsystem: atom(),
          payload_schema: pos_integer(),
          converter: module(),
          catalog_case: atom() | nil,
          explanation: String.t()
        }
end

defmodule Cure.Diagnostic.Registry do
  @moduledoc "Typed ownership and reachability metadata for every stable diagnostic code."

  alias Cure.Diagnostic.Registry.Entry

  @retired ~w[E015 E018]
  @structured ~w[E035 E063 E068 E070 E091 E092 E093 E094 E095 E096 E097 E098 E099 E100 E101 W000 W001 W002]
  @catalog_cases %{
    "E068" => :export_unmappable,
    "E070" => :snap_missing,
    "E091" => :unknown_name,
    "E092" => :macro_expansion,
    "E093" => :type_mismatch,
    "E094" => :syntax_error,
    "E095" => :file_read,
    "E096" => :file_write,
    "E097" => :dependency,
    "E098" => :command,
    "E099" => :usage,
    "E100" => :artifact,
    "W000" => :compiler_warning,
    "W001" => :migration_warning,
    "W002" => :configuration_warning
  }

  @spec entries() :: [Entry.t()]
  def entries do
    Cure.Compiler.Errors.list_all()
    |> Enum.map(fn {code, title, brief} ->
      %Entry{
        code: code,
        key: stable_key(code, title),
        severity: severity(code),
        title: title,
        status: if(code in @retired, do: :retired, else: :reachable),
        subsystem: subsystem(code),
        payload_schema: 1,
        converter: converter(code),
        catalog_case: Map.get(@catalog_cases, code),
        explanation: brief
      }
    end)
  end

  @spec fetch(String.t()) :: {:ok, Entry.t()} | :error
  def fetch(code) when is_binary(code) do
    normalized = String.upcase(code)

    case Enum.find(entries(), &(&1.code == normalized)) do
      nil -> :error
      entry -> {:ok, entry}
    end
  end

  @spec fetch!(String.t()) :: Entry.t()
  def fetch!(code) do
    case fetch(code) do
      {:ok, entry} -> entry
      :error -> raise ArgumentError, "unregistered diagnostic code: #{inspect(code)}"
    end
  end

  @spec reachable() :: [Entry.t()]
  def reachable, do: Enum.filter(entries(), &(&1.status == :reachable))

  @spec retired() :: [Entry.t()]
  def retired, do: Enum.filter(entries(), &(&1.status == :retired))

  defp severity("E" <> _), do: :error
  defp severity("W" <> _), do: :warning
  defp severity("I" <> _), do: :information
  defp severity("H" <> _), do: :hint

  defp stable_key("E091", _title), do: :unknown_name
  defp stable_key("E092", _title), do: :macro_expansion_failed
  defp stable_key("E093", _title), do: :type_mismatch
  defp stable_key("E094", _title), do: :syntax_error
  defp stable_key("E101", _title), do: :internal_compiler_error

  defp stable_key(_code, title) do
    title
    |> String.downcase()
    |> String.replace(~r/[^a-z0-9]+/, "_")
    |> String.trim("_")
    |> String.to_atom()
  end

  defp converter(code) when code in @structured, do: Cure.Diagnostic.Adapter
  defp converter(_code), do: Cure.Compiler.Errors

  defp subsystem("E101"), do: :compiler
  defp subsystem("E091"), do: :resolution
  defp subsystem("E092"), do: :macros
  defp subsystem("E093"), do: :elaboration
  defp subsystem("E094"), do: :parser
  defp subsystem(code) when code in ~w[E095 E096 E097 E098 E099 E100], do: :operations
  defp subsystem("W" <> _), do: :analysis
  defp subsystem(_code), do: :compiler
end
