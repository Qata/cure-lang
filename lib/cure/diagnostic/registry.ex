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

  @retired ~w[E001 E004 E005 E006 E007 E009 E010 E012 E015 E016 E017 E018 E019 E020 E023 E024 E025 E027 E028 E029 E031 E032 E033 E034 E036 E037 E064 E071 E072 E073 E074 E075 E079 E080 E085 H083 H084 W081 W082]
  @operational ~w[E008 E030 E038 E039 E040 E041 E042 E065 E066 E067 E068 E069 E070 E095 E096 E097 E098 E099 E100 E101 W000 W001 W002]
  @retirement_reasons %{
    "E001" => "No first-party producer remains; contextual E093 is the active type-mismatch path.",
    "E004" => "No first-party producer remains; match coverage is not emitted as this catalog code.",
    "E005" => "No first-party producer remains; guard constraints are reported through contextual checking.",
    "E006" => "No first-party producer remains; effect failures use contextual checking diagnostics.",
    "E007" => "No first-party producer remains; unused-variable analysis is not emitted by the compiler.",
    "E009" => "No first-party producer remains; unreachable-clause analysis is not emitted by the compiler.",
    "E010" => "No first-party producer remains; effect annotations are checked contextually.",
    "E012" => "No first-party producer remains; sigma failures use dependent type diagnostics.",
    "E015" => "The former error path was consolidated into the contextual declaration diagnostics.",
    "E016" => "No first-party producer remains; dependent mismatches use contextual E093 diagnostics.",
    "E017" => "No first-party producer remains; equality failures use contextual E093 diagnostics.",
    "E018" => "The former error path was consolidated into the contextual declaration diagnostics.",
    "E019" => "No first-party producer remains; implicit failures use E011.",
    "E020" => "No first-party producer remains; doctest reporting is not emitted by the compiler.",
    "E023" => "No first-party producer remains; map-pattern keys are rejected by generic syntax handling.",
    "E024" => "No first-party producer remains; pin failures are not emitted as this catalog code.",
    "E025" => "No first-party producer remains; nested coverage is not emitted as this catalog code.",
    "E027" => "No first-party producer remains; assert_type failures use contextual E093 diagnostics.",
    "E028" => "No first-party producer remains; record defaults use contextual type checking.",
    "E029" => "No first-party producer remains; mutual-recursion structural checks are not emitted as this code.",
    "E031" => "No first-party producer remains; binary coverage is not emitted as this catalog code.",
    "E032" => "No first-party producer remains; unreachable match clauses are not emitted as this code.",
    "E033" => "No first-party producer remains; branch joins use contextual E093 diagnostics.",
    "E034" => "No first-party producer remains; let-pattern coverage is not emitted as this code.",
    "E036" => "No first-party producer remains; binary comprehension failures use generic syntax handling.",
    "E037" => "No first-party producer remains; binary segment failures use generic type checking.",
    "E064" => "No first-party producer remains; monomorphisation budget warnings are not emitted.",
    "E071" => "No first-party producer remains; function payload failures use name/type diagnostics.",
    "E072" => "No first-party producer remains; multiline type layout failures use syntax diagnostics.",
    "E073" => "No first-party producer remains; empty pickup blocks use E076.",
    "E074" => "No first-party producer remains; nullary pattern failures use pattern diagnostics.",
    "E075" => "No first-party producer remains; constructor arity failures use contextual checking.",
    "E079" => "No first-party producer remains; pickup guards use contextual E093 diagnostics.",
    "E080" => "No first-party producer remains; pickup branch joins use contextual E093 diagnostics.",
    "E085" => "The legacy if migration is emitted as a migration event, not a compiler diagnostic.",
    "H083" => "Formatter normalization is not emitted as a diagnostic code.",
    "H084" => "Formatter normalization is not emitted as a diagnostic code.",
    "W081" => "No first-party producer remains; pickup reachability warnings are not emitted.",
    "W082" => "No first-party producer remains; pickup reachability warnings are not emitted."
  }
  @structured ~w[E002 E003 E011 E013 E014 E021 E022 E026 E035 E056 E057 E063 E076 E077 E078 E087 E089 E090 E091 E092 E093 E094 E102 E103 E104 E105 E106 E107 E108 W086 W088]
  @known_producers ~w[
    dependency_graph doctor elaboration kernel kernel_conversion lexer macro_expansion
    module_loader name_resolution operational parser pattern_checker proof_checker
    totality_checker
  ]a
  @producer_modules %{
    dependency_graph: Cure.Compiler.DepGraph,
    doctor: Cure.Doctor,
    elaboration: Cure.Elab.Program,
    kernel: Cure.Core.Kernel,
    kernel_conversion: Cure.Elab.TypeConv,
    lexer: Cure.Compiler.Lexer,
    macro_expansion: Cure.Elab.MacroExpand,
    module_loader: Cure.Compiler.Incremental,
    name_resolution: Cure.Elab.Resolution,
    operational: Cure.Diagnostic.Operational,
    parser: Cure.Compiler.Parser,
    pattern_checker: Cure.Elab.Elaborator,
    proof_checker: Cure.Elab.ProofSearch,
    totality_checker: Cure.Elab.TotalityClosure
  }
  @catalog_cases %{
    "E002" => :unbound_variable,
    "E008" => :undocumented_public_function,
    "E003" => :arity_mismatch,
    "E011" => :missing_implicit,
    "E013" => :totality_failure,
    "E014" => :unfilled_hole,
    "E021" => :unknown_record,
    "E022" => :record_field_mismatch,
    "E026" => :proof_shape_mismatch,
    "E030" => :package_version_conflict,
    "E035" => :unterminated_lambda,
    "E041" => :registry_signature_invalid,
    "E042" => :transparency_log_unreachable,
    "E038" => :registry_fetch_failed,
    "E039" => :registry_hash_mismatch,
    "E040" => :registry_package_not_found,
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
    "E102" => :erasure_violation,
    "E103" => :non_strictly_positive_type,
    "E104" => :erased_value_used_relevantly,
    "E105" => :declaration_conflict,
    "E106" => :operator_declaration_conflict,
    "E107" => :unsupported_async,
    "E108" => :splice_outside_quote,
    "W000" => :compiler_warning,
    "W001" => :migration_warning,
    "W002" => :configuration_warning,
    "W086" => :import_cycle,
    "W088" => :unresolved_import
  }

  @spec entries() :: [Entry.t()]
  def entries do
    Cure.Diagnostic.Registry.Catalog.entries()
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
        explanation: Cure.Diagnostic.Registry.Catalog.explanation!(code)
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

  @doc "Return the checked code-to-producer inventory used by CI and catalog tooling."
  @spec producer_inventory() :: %{String.t() => [atom()]}
  def producer_inventory do
    Map.new(entries(), &{&1.code, &1.producers})
  end

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
         :ok <- unique_catalog_metadata(entries),
         :ok <- valid_entries(entries) do
      :ok
    end
  end

  @doc "Verify that reachable codes and declared producers have first-party source evidence."
  @spec validate_reachability([Path.t()]) :: :ok | {:error, term()}
  def validate_reachability(paths \\ default_producer_paths()) when is_list(paths) do
    referenced =
      paths
      |> Enum.flat_map(&source_codes/1)
      |> MapSet.new()

    missing_codes =
      reachable()
      |> Enum.reject(&MapSet.member?(referenced, &1.code))
      |> Enum.map(& &1.code)
      |> Enum.sort()

    with :ok <- if(missing_codes == [], do: :ok, else: {:error, {:unreachable_code, missing_codes}}),
         :ok <- validate_producer_coverage(),
         :ok <- validate_producer_catalog() do
      :ok
    end
  end

  @doc "Ensure every known producer owns a reachable registry entry."
  @spec validate_producer_coverage() :: :ok | {:error, term()}
  def validate_producer_coverage do
    owned =
      reachable()
      |> Enum.flat_map(& &1.producers)
      |> MapSet.new()

    missing = @known_producers |> Enum.reject(&MapSet.member?(owned, &1)) |> Enum.sort()
    if missing == [], do: :ok, else: {:error, {:producer_without_reachable_code, missing}}
  end

  @doc "Ensure every known producer has a reachable catalog fixture for a public path."
  @spec validate_producer_catalog() :: :ok | {:error, {:producer_without_catalog_fixture, [atom()]}}
  def validate_producer_catalog do
    missing =
      @known_producers
      |> Enum.reject(fn producer ->
        Enum.any?(reachable(), fn entry ->
          producer in entry.producers and not is_nil(entry.catalog_case) and not is_nil(entry.fixture_id)
        end)
      end)

    if missing == [], do: :ok, else: {:error, {:producer_without_catalog_fixture, missing}}
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
  defp stable_key("E102", _title), do: :erasure_violation
  defp stable_key("E103", _title), do: :non_strictly_positive_type
  defp stable_key("E104", _title), do: :erased_value_used_relevantly
  defp stable_key("E105", _title), do: :declaration_conflict
  defp stable_key("E106", _title), do: :operator_declaration_conflict
  defp stable_key("E107", _title), do: :unsupported_async
  defp stable_key("E108", _title), do: :splice_outside_quote

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
       when code in ~w[E030 E038 E039 E040 E041 E042 E065 E066 E067 E068 E069 E070 E095 E096 E097 E098 E099 E100 W000 W001 W002],
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
  defp producers("E092"), do: [:macro_expansion, :parser]
  defp producers("E093"), do: [:elaboration, :kernel, :kernel_conversion]
  defp producers("E094"), do: [:lexer, :parser]
  defp producers("E101"), do: [:operational, :kernel]
  defp producers("E102"), do: [:elaboration]
  defp producers("E103"), do: [:kernel]
  defp producers("E104"), do: [:elaboration]
  defp producers("E105"), do: [:elaboration, :name_resolution]
  defp producers("E106"), do: [:parser, :elaboration]
  defp producers("E107"), do: [:elaboration]
  defp producers("E108"), do: [:elaboration]
  defp producers("E008"), do: [:doctor]
  defp producers("W086"), do: [:dependency_graph]
  defp producers("W088"), do: [:name_resolution]
  defp producers(_code), do: [:compiler_errors]

  defp subsystem("E101"), do: :compiler
  defp subsystem("E102"), do: :elaboration
  defp subsystem("E103"), do: :kernel
  defp subsystem("E104"), do: :elaboration
  defp subsystem("E105"), do: :elaboration
  defp subsystem("E106"), do: :elaboration
  defp subsystem("E107"), do: :elaboration
  defp subsystem("E108"), do: :elaboration
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

  defp unique_catalog_metadata(entries) do
    reachable = Enum.filter(entries, &(&1.status == :reachable))

    with :ok <- unique_field(reachable, :catalog_case, :duplicate_catalog_case),
         :ok <- unique_field(reachable, :fixture_id, :duplicate_fixture_id) do
      :ok
    end
  end

  defp unique_field(entries, field, error_tag) do
    case entries |> Enum.group_by(&Map.fetch!(&1, field)) |> Enum.find(fn {_value, owners} -> length(owners) > 1 end) do
      {value, _owners} -> {:error, {error_tag, value}}
      nil -> :ok
    end
  end

  defp valid_entries(entries) do
    Enum.find_value(entries, :ok, &validate_entry/1)
  end

  defp default_source_paths do
    Path.wildcard("lib/**/*.ex")
  end

  defp default_producer_paths do
    default_source_paths()
    |> Enum.reject(&String.contains?(&1, "lib/cure/diagnostic/registry"))
  end

  defp validate_entry(%Entry{} = entry) do
    cond do
      entry.producers == [] ->
        {:error, {:missing_producer, entry.code}}

      entry.status == :reachable and
          Enum.any?(entry.producers, &(&1 not in @known_producers)) ->
        {:error, {:unowned_producer, entry.code}}

      entry.status == :reachable and
          Enum.any?(entry.producers, &(not producer_loaded?(&1))) ->
        {:error, {:unreachable_producer, entry.code}}

      entry.status == :reachable and entry.converter == Cure.Compiler.Errors ->
        {:error, {:legacy_converter, entry.code}}

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

      entry.status == :reachable and is_nil(entry.catalog_case) ->
        {:error, {:reachable_without_catalog_case, entry.code}}

      entry.status == :reachable and is_nil(entry.fixture_id) ->
        {:error, {:reachable_without_fixture, entry.code}}

      true ->
        :ok
    end
  end

  defp producer_loaded?(producer) do
    case Map.fetch(@producer_modules, producer) do
      {:ok, module} -> Code.ensure_loaded?(module)
      :error -> false
    end
  end
end
