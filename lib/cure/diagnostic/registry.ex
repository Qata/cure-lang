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
    :schema_version,
    :producers,
    :converter,
    :converter_function,
    :catalog_case,
    :fixture_id,
    :retirement_reason,
    :brief,
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
          schema_version: pos_integer(),
          producers: [atom(), ...],
          converter: module(),
          converter_function: atom(),
          catalog_case: atom() | nil,
          fixture_id: atom() | nil,
          retirement_reason: String.t() | nil,
          brief: String.t(),
          explanation: String.t()
        }
end

defmodule Cure.Diagnostic.Registry do
  @moduledoc "Typed ownership and reachability metadata for every stable diagnostic code."

  alias Cure.Diagnostic.Registry.Entry

  @retired ~w[E015 E018]
  @operational ~w[E041 E042 E065 E066 E067 E068 E069 E070 E095 E096 E097 E098 E099 E100 E101 W000 W001 W002]
  @retirement_reasons %{
    "E015" => "The former error path was consolidated into the contextual declaration diagnostics.",
    "E018" => "The former error path was consolidated into the contextual declaration diagnostics."
  }
  @structured ~w[E002 E003 E011 E013 E014 E021 E022 E026 E035 E056 E057 E063 E076 E077 E078 E087 E089 E090 E091 E092 E093 E094 W086 W088]
  @catalog_cases %{
    "E002" => :unbound_variable,
    "E003" => :arity_mismatch,
    "E011" => :missing_implicit,
    "E013" => :totality_failure,
    "E014" => :unfilled_hole,
    "E021" => :unknown_record,
    "E022" => :record_field_mismatch,
    "E026" => :proof_shape_mismatch,
    "E035" => :unterminated_lambda,
    "E041" => :registry_signature_invalid,
    "E042" => :transparency_log_unreachable,
    "E056" => :extern_untyped_head,
    "E057" => :extern_has_body,
    "E076" => :pickup_missing_else,
    "E077" => :pickup_else_not_last,
    "E078" => :pickup_multiple_else,
    "E063" => :parse_recovered,
    "E065" => :proof_file_missing,
    "E066" => :proof_verification_failed,
    "E067" => :proof_schema_incompatible,
    "E069" => :snap_schema_incompatible,
    "E087" => :duplicate_module,
    "E089" => :ambiguous_name,
    "E068" => :export_unmappable,
    "E070" => :snap_missing,
    "E091" => :unknown_name,
    "E090" => :unrecognized_pattern,
    "E092" => :macro_expansion,
    "E093" => :type_mismatch,
    "E094" => :syntax_error,
    "E095" => :file_read,
    "E096" => :file_write,
    "E097" => :dependency,
    "E098" => :command,
    "E099" => :usage,
    "E100" => :artifact,
    "E101" => :internal_compiler_error,
    "W000" => :compiler_warning,
    "W001" => :migration_warning,
    "W002" => :configuration_warning,
    "W086" => :import_cycle,
    "W088" => :unresolved_import
  }

  @spec entries() :: [Entry.t()]
  def entries do
    Cure.Compiler.Errors.catalog_entries()
    |> Enum.map(fn {code, title, brief} ->
      %Entry{
        code: code,
        key: stable_key(code, title),
        severity: severity(code),
        title: title,
        status: if(code in @retired, do: :retired, else: :reachable),
        subsystem: subsystem(code),
        payload_schema: 1,
        schema_version: 1,
        producers: producers(code),
        converter: converter(code),
        converter_function: converter_function(code),
        catalog_case: Map.get(@catalog_cases, code),
        fixture_id: Map.get(@catalog_cases, code),
        retirement_reason: Map.get(@retirement_reasons, code),
        brief: brief,
        explanation: Cure.Compiler.Errors.catalog_explanation!(code)
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

  @doc "Return the legacy explain-list shape derived from typed registry entries."
  @spec list_all() :: [{String.t(), String.t(), String.t()}]
  def list_all do
    entries()
    |> Enum.map(&{&1.code, &1.title, &1.brief})
    |> Enum.sort_by(&elem(&1, 0))
  end

  @doc "Look up the complete explanation for a registered diagnostic code."
  @spec explain(String.t()) :: {:ok, String.t()} | :error
  def explain(code) when is_binary(code) do
    case fetch(code) do
      {:ok, entry} -> {:ok, entry.explanation}
      :error -> :error
    end
  end

  @doc "Validate registry invariants used by the diagnostic catalog and CI."
  @spec validate([Entry.t()]) :: :ok | {:error, term()}
  def validate(entries \\ entries()) when is_list(entries) do
    with :ok <- unique_codes(entries),
         :ok <- valid_entries(entries) do
      :ok
    end
  end

  @doc "Validate stable diagnostic codes referenced by first-party source files."
  @spec validate_sources([Path.t()]) :: :ok | {:error, {:unregistered_source_codes, [String.t()]}}
  def validate_sources(paths \\ default_source_paths()) when is_list(paths) do
    referenced =
      paths
      |> Enum.flat_map(&source_codes/1)
      |> MapSet.new()

    registered = entries() |> Enum.map(& &1.code) |> MapSet.new()
    missing = referenced |> MapSet.difference(registered) |> Enum.sort()

    if missing == [], do: :ok, else: {:error, {:unregistered_source_codes, missing}}
  end

  @doc false
  @spec source_codes(Path.t()) :: [String.t()]
  def source_codes(path) do
    case File.read(path) do
      {:ok, source} ->
        Regex.scan(~r/[\"']((?:E|W|I|H)\d{3})[\"']/, source, capture: :all_but_first)
        |> List.flatten()
        |> Enum.uniq()

      {:error, _reason} ->
        []
    end
  end

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

  defp converter(code) when code in @operational, do: Cure.Diagnostic.Operational
  defp converter(code) when code in @structured, do: Cure.Diagnostic.Adapter
  defp converter(_code), do: Cure.Compiler.Errors

  defp converter_function(code) when code in @operational, do: :from_error
  defp converter_function(code) when code in @structured, do: :from_error
  defp converter_function(_code), do: :format_error

  defp producers(code)
       when code in ~w[E041 E042 E065 E066 E067 E068 E069 E070 E095 E096 E097 E098 E099 E100 W000 W001 W002],
       do: [:operational]

  defp producers(code) when code in ~w[E011 E014], do: [:elaboration]
  defp producers("E013"), do: [:totality_checker]
  defp producers(code) when code in ~w[E021 E022], do: [:elaboration]
  defp producers("E026"), do: [:proof_checker]
  defp producers("E002"), do: [:name_resolution, :kernel]
  defp producers("E003"), do: [:elaboration, :kernel]
  defp producers("E035"), do: [:parser]
  defp producers(code) when code in ~w[E056 E057], do: [:elaboration]
  defp producers(code) when code in ~w[E076 E077 E078], do: [:parser]
  defp producers("E063"), do: [:parser]
  defp producers("E087"), do: [:module_loader]
  defp producers("E089"), do: [:name_resolution]
  defp producers("E090"), do: [:elaboration, :kernel_conversion]
  defp producers("E091"), do: [:name_resolution, :pattern_checker]
  defp producers("E092"), do: [:macro_expansion]
  defp producers("E093"), do: [:elaboration, :kernel_conversion]
  defp producers("E094"), do: [:lexer, :parser]
  defp producers("E101"), do: [:operational]
  defp producers("W086"), do: [:dependency_graph]
  defp producers("W088"), do: [:name_resolution]
  defp producers(_code), do: [:compiler_errors]

  defp subsystem("E101"), do: :compiler
  defp subsystem("E091"), do: :resolution
  defp subsystem("E092"), do: :macros
  defp subsystem("E093"), do: :elaboration
  defp subsystem("E094"), do: :parser
  defp subsystem(code) when code in ~w[E095 E096 E097 E098 E099 E100], do: :operations
  defp subsystem("W" <> _), do: :analysis
  defp subsystem(_code), do: :compiler

  defp unique_codes(entries) do
    entries
    |> Enum.map(& &1.code)
    |> Enum.frequencies()
    |> Enum.find_value(:ok, fn
      {code, count} when count > 1 -> {:error, {:duplicate_code, code}}
      _ -> nil
    end)
  end

  defp valid_entries(entries) do
    Enum.find_value(entries, :ok, &validate_entry/1)
  end

  defp default_source_paths do
    Path.wildcard("lib/**/*.ex")
  end

  defp validate_entry(%Entry{} = entry) do
    cond do
      entry.producers == [] ->
        {:error, {:missing_producer, entry.code}}

      not is_atom(entry.converter) ->
        {:error, {:missing_converter, entry.code}}

      not is_atom(entry.converter_function) ->
        {:error, {:missing_converter_function, entry.code}}

      not Code.ensure_loaded?(entry.converter) or
          not function_exported?(entry.converter, entry.converter_function, 2) ->
        {:error, {:missing_converter_function, entry.code}}

      not is_integer(entry.schema_version) or entry.schema_version < 1 ->
        {:error, {:invalid_schema_version, entry.code}}

      entry.status == :retired and (not is_binary(entry.retirement_reason) or entry.retirement_reason == "") ->
        {:error, {:retired_without_reason, entry.code}}

      entry.status == :reachable and not is_nil(entry.retirement_reason) ->
        {:error, {:reachable_with_retirement_reason, entry.code}}

      true ->
        :ok
    end
  end
end
