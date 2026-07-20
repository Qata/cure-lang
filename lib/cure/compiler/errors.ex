defmodule Cure.Compiler.Errors do
  @moduledoc """
  Formats compiler errors into human-readable messages with source locations.

  Handles errors from every pipeline stage: lexer, parser, type checker,
  and code generation.

  ## Example output

      error: type mismatch in function 'bad'
       --> hello.cure:3
        | declared return type Int but body has type String
  """

  @doc """
  Format a compiler error into a human-readable string.

  Accepts error tuples from any pipeline stage and a file path for context.
  """
  @spec format_error(term(), String.t()) :: String.t()
  def format_error(error, file \\ "nofile")

  def format_error(%Cure.Diagnostic{} = diagnostic, file) do
    body = Cure.Diagnostic.message(diagnostic)

    extras =
      (Enum.map(diagnostic.notes, &Cure.Diagnostic.Doc.plain(&1, width: 1_000_000)) ++
         Enum.map(diagnostic.suggestions, & &1.message))
      |> Enum.join(" ")

    body = [body, extras] |> Enum.reject(&(&1 == "")) |> Enum.join(" ") |> String.replace(~r/\s+/, " ")

    location =
      case diagnostic.primary do
        %Cure.Diagnostic.Label{span: %{start_line: line}} when is_integer(line) and line > 0 ->
          "#{file}:#{line}"

        _ ->
          file
      end

    "-- #{String.upcase(diagnostic.title)} [#{diagnostic.code}]\n--> #{location}\n#{body}"
  end

  def format_error({:unknown_global, _name} = error, file) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:unknown_global, _name, details} = error, file) when is_map(details) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:unknown_name, details} = error, file) when is_map(details) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:codegen_error, {:unknown_global, _name}} = error, file) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:codegen_error, {:unknown_global, _name, details}} = error, file) when is_map(details) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:unknown_constructor, _name} = error, file) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:lift_module_error, details} = error, file) when is_map(details) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:conversion_failure, _actual, _expected} = error, file) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({kind, _, _} = error, file)
      when kind in [:unbound_variable, :arity_mismatch, :ambiguous_name, :duplicate_module] do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:import_cycle, _} = error, file) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:unresolved_import, _, _, _, _} = error, file) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  def format_error({:extern_arity_mismatch, _, _, _} = error, file) do
    error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)
  end

  # -- Type Errors -------------------------------------------------------------

  def format_error(errors, file) when is_list(errors) do
    # A bare list reaches this clause from `Cure.Types.Checker.check_module/2`,
    # which returns `{:error, errors}` directly; joining with a blank line
    # keeps multi-error output readable.
    Enum.map_join(errors, "\n\n", &format_error(&1, file))
  end

  def format_error({:type_error, errors}, file) when is_list(errors) do
    format_error(errors, file)
  end

  def format_error({:type_mismatch, message, meta}, file) do
    {:type_mismatch, message, meta}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:unknown_erasure_class, name, class}, file) do
    {:unknown_erasure_class, name, class}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:erases_on_non_opaque, name}, file) do
    {:erases_on_non_opaque, name}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:unsupported_async, message, meta}, file) do
    {:unsupported_async, message, meta}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:splice_outside_quote, tag, meta}, file) do
    {:splice_outside_quote, tag, meta}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:extern_untyped_head, message, meta}, file) do
    {:extern_untyped_head, message, meta}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:extern_has_body, message, meta}, file) do
    {:extern_has_body, message, meta}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  # -- Parse Errors ------------------------------------------------------------

  def format_error({:parse_error, errors}, file) when is_list(errors) do
    format_error(errors, file)
  end

  def format_error({:unexpected_token, _, _, _} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  def format_error({:parse_recovered, _, _, _} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  def format_error({:expected, _, :got, _, _, _} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  def format_error({:expected_token, _, _, _, _, _} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  def format_error({:lambda_block_unterminated, _, _, _} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  # -- Lex Errors --------------------------------------------------------------

  def format_error({:lex_error, _reason} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  # -- Codegen Errors ----------------------------------------------------------

  def format_error({:codegen_error, {:computed_macro_error, _meta, _reason} = error}, file),
    do: format_error(error, file)

  def format_error({:codegen_error, reason}, file) do
    {:codegen_error, reason}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:beam_lint_error, errors, warnings}, file) do
    {:beam_lint_error, errors, warnings}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:beam_lint_error, errors}, file) do
    {:beam_lint_error, errors}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:expected_module, _ast}, file) do
    {:expected_module, nil}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:unsupported_container, type}, file) do
    {:unsupported_container, type}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  # -- File Errors -------------------------------------------------------------

  def format_error({:file_read_error, path, reason}, _file) do
    Cure.Diagnostic.Operational.from_error({:file_read_error, path, reason})
    |> format_error(path)
  end

  # -- DepGraph / Build-Order Errors -------------------------------------------

  # -- Edition Errors ----------------------------------------------------------

  def format_error({:edition_pragma_placement, line, col}, file) do
    {:edition_pragma_placement, line, col}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:edition_pragma_malformed, line, col}, file) do
    {:edition_pragma_malformed, line, col}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:edition_pragma_unknown, line, col}, file) do
    {:edition_pragma_unknown, line, col}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:edition_error, {:unknown_edition, edition}}, file) do
    {:edition_error, {:unknown_edition, edition}}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  # -- Macro error floor (SP1 §2) ----------------------------------------------

  def format_error({:macro_use_mismatch, keyword, expected, got, line, col}, file) do
    {:macro_use_mismatch, keyword, expected, got, line, col}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:malformed_hole, line, col}, file) do
    {:malformed_hole, line, col}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:missing_diagnosis, points}, file) do
    {:missing_diagnosis, points}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:rule_unpinned, keywords}, file) do
    {:rule_unpinned, keywords}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:example_mismatch, mismatches}, file) do
    {:example_mismatch, mismatches}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:example_type_mismatch, failures}, file) do
    {:example_type_mismatch, failures}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:computed_example_error, failures}, file) do
    {:computed_example_error, failures}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  def format_error({:computed_macro_error, meta, reason}, file) do
    {:computed_macro_error, meta, reason}
    |> Cure.Diagnostic.Adapter.from_error(span: macro_span(file, meta))
    |> format_error(file)
  end

  def format_error({:expansion_ill_typed, details}, file) do
    {:expansion_ill_typed, details}
    |> Cure.Diagnostic.Adapter.from_error()
    |> format_error(file)
  end

  # -- Exhaustiveness guard ----------------------------------------------------

  def format_error(error, file) do
    raise Cure.Diagnostic.UnhandledError, error: %{error: error, file: file}
  end

  defp macro_span(file, meta) do
    line = Keyword.get(meta, :line, 1)
    column = Keyword.get(meta, :col, Keyword.get(meta, :column, 1))

    %Cure.Diagnostic.Span{
      source_id: {:compiler_source, file},
      path: file,
      start_byte: 0,
      end_byte: 0,
      start_line: max(line, 1),
      end_line: max(line, 1),
      start_column: max(column, 1),
      end_column: max(column, 1)
    }
  end

  # -- "Did you mean?" Suggestions ---------------------------------------------

  # -- Error Catalog ------------------------------------------------------------

  @doc """
  Look up an error code explanation.

  Returns `{:ok, text}` or `:error` if the code is unknown.
  """
  @spec explain(String.t()) :: {:ok, String.t()} | :error
  def explain(code), do: Cure.Diagnostic.Registry.explain(code)

  @doc """
  Return all known error codes with a one-line summary each.

  Each element is `{code, title, brief}` where `title` is the short name
  (e.g. "Type Mismatch") and `brief` is the first descriptive sentence.
  The list is sorted by code.
  """
  @spec list_all() :: [{String.t(), String.t(), String.t()}]
  def list_all, do: Cure.Diagnostic.Registry.list_all()

  @doc false
  @spec catalog_explanation!(String.t()) :: String.t()
  def catalog_explanation!(code), do: Cure.Diagnostic.Registry.Catalog.explanation!(code)

  @doc false
  @spec catalog_entries() :: [{String.t(), String.t(), String.t()}]
  def catalog_entries, do: Cure.Diagnostic.Registry.Catalog.entries()

  @doc """
  Suggest similar names for typos using Levenshtein distance.

  Both `name` and every entry in `candidates` are coerced to strings
  before comparison. Atoms are converted via `Atom.to_string/1`; any
  other shape (including `nil`) is dropped from the candidate list and
  causes `nil` to be returned when it appears as the `name`. This
  defends against atom keys leaking out of the type-environment scope
  maps (e.g. the lexer keyword `:else`), which would otherwise crash
  `String.length/1` deep inside the Levenshtein loop.
  """
  @spec suggest(term(), [term()]) :: String.t() | nil
  def suggest(name, candidates) do
    case to_string_safe(name) do
      nil ->
        nil

      name_str ->
        candidates
        |> Enum.map(&to_string_safe/1)
        |> Enum.filter(&is_binary/1)
        |> Enum.map(fn c -> {c, levenshtein(name_str, c)} end)
        |> Enum.filter(fn {_, d} -> d > 0 and d <= 2 end)
        |> Enum.sort_by(fn {_, d} -> d end)
        |> case do
          [{best, _} | _] -> best
          _ -> nil
        end
    end
  end

  # Best-effort coercion to a binary; returns `nil` for anything that
  # cannot be sensibly displayed as text.
  defp to_string_safe(value) when is_binary(value), do: value
  defp to_string_safe(value) when is_atom(value) and not is_nil(value), do: Atom.to_string(value)
  defp to_string_safe(_), do: nil

  @doc """
  Format an error with source context showing the offending line.
  """
  @spec format_with_source(term(), String.t(), String.t()) :: String.t()
  def format_with_source(error, file, source) do
    if structured_error?(error) do
      {diagnostic, registry} = to_diagnostic(error, file, source)
      Cure.Diagnostic.Renderer.plain(diagnostic, registry)
    else
      format_legacy_with_source(error, file, source)
    end
  end

  @doc "Convert an error at the compiler presentation boundary."
  @spec to_diagnostic(term(), String.t(), String.t()) ::
          {Cure.Diagnostic.t(), Cure.Diagnostic.SourceRegistry.t()}
  def to_diagnostic(error, file, source) do
    source_id = {:compiler_source, file}

    registry =
      Cure.Diagnostic.SourceRegistry.new()
      |> Cure.Diagnostic.SourceRegistry.register(source_id, source, file)

    opts =
      case exact_error_span(error, source, source_id, registry) do
        {:ok, span} -> [span: span]
        :error -> []
      end

    diagnostic =
      if operational_error?(error) do
        Cure.Diagnostic.Operational.from_error(error)
      else
        Cure.Diagnostic.Adapter.from_error(error, opts)
      end

    {diagnostic, registry}
  end

  defp format_legacy_with_source(error, file, source) do
    base = format_error(error, file)
    line_num = extract_line(error)

    if line_num > 0 and source != "" do
      lines = String.split(source, "\n")

      case Enum.at(lines, line_num - 1) do
        nil ->
          base

        src_line ->
          col = extract_col(error)
          caret = if col > 0, do: "\n      | #{String.duplicate(" ", col - 1)}^", else: ""
          base <> "\n      | #{src_line}" <> caret
      end
    else
      base
    end
  end

  defp structured_error?({:unknown_global, _name}), do: true
  defp structured_error?({:unknown_global, _name, details}) when is_map(details), do: true
  defp structured_error?({:unknown_name, details}) when is_map(details), do: true
  defp structured_error?({:codegen_error, {:unknown_global, _name}}), do: true
  defp structured_error?({:codegen_error, {:unknown_global, _name, details}}) when is_map(details), do: true
  defp structured_error?({:unknown_constructor, _name}), do: true
  defp structured_error?({:type_mismatch, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:type_error, errors}) when is_list(errors), do: true
  defp structured_error?({:unknown_erasure_class, _name, _class}), do: true
  defp structured_error?({:erases_on_non_opaque, _name}), do: true
  defp structured_error?({:non_strictly_positive, _family}), do: true
  defp structured_error?({:erased_used_relevantly, details}) when is_map(details), do: true
  defp structured_error?({:usage_violation, details}) when is_map(details), do: true
  defp structured_error?({:duplicate_type, _name}), do: true
  defp structured_error?({:duplicate_ctor, _name}), do: true
  defp structured_error?({:duplicate_field, _name}), do: true
  defp structured_error?({:duplicate_parameter, _name}), do: true
  defp structured_error?({:reserved_union_type_name, _name}), do: true
  defp structured_error?({:constructor_function_collision, _name}), do: true
  defp structured_error?({:duplicate_definition, _name}), do: true
  defp structured_error?({:overlapping_overload, _name, _arity}), do: true
  defp structured_error?({:sibling_module_collision, _name, _owners}), do: true
  defp structured_error?({:precedence_cycle, _groups}), do: true
  defp structured_error?({:builtin_operator_not_overloadable, _operator}), do: true
  defp structured_error?({:unsupported_operand_type, _operator}), do: true
  defp structured_error?({:no_operator_meaning, _operator}), do: true
  defp structured_error?({:unsupported_async, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:splice_outside_quote, _tag, meta}) when is_list(meta), do: true
  defp structured_error?({:unbound_variable, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:arity_mismatch, _message, meta}) when is_list(meta), do: true

  defp structured_error?({:extern_arity_mismatch, _name, declared, present})
       when is_integer(declared) and is_integer(present),
       do: true

  defp structured_error?({:constructor_arity_mismatch, _name}), do: true
  defp structured_error?({:tuple_arity_mismatch, _direction, _details}), do: true
  defp structured_error?({:with_rematch_arity_mismatch, _expected, _actual}), do: true
  defp structured_error?({:typed_pattern_type_mismatch, _type_ast}), do: true

  defp structured_error?({:extern_untyped_head, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:extern_has_body, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:unknown_record, _name}), do: true
  defp structured_error?({:unknown_field, _record, _field}), do: true
  defp structured_error?({:record_field_mismatch, _name}), do: true
  defp structured_error?({:unknown_type, _name}), do: true
  defp structured_error?({:unknown_module, _name}), do: true
  defp structured_error?({:unknown_member, _module, _name}), do: true
  defp structured_error?({:projection_non_record, _field}), do: true
  defp structured_error?({:proof_shape_mismatch, _message, _name}), do: true
  defp structured_error?({:ambiguous_proof_search, _goal, candidates}) when is_list(candidates), do: true
  defp structured_error?({:totality_required, _name}), do: true
  defp structured_error?({:compile_time_totality, _name, _reason}), do: true

  defp structured_error?({kind, _message, meta})
       when kind in [:pickup_no_else, :pickup_else_not_last, :pickup_multiple_else] and is_list(meta),
       do: true

  defp structured_error?({:duplicate_module_identity, _name, _other_path, _path}), do: true
  defp structured_error?({:duplicate_module_identity, _name, paths}) when is_list(paths), do: true
  defp structured_error?({:unfilled_hole, _name}), do: true
  defp structured_error?({:unsolved_metavariables, _name}), do: true
  defp structured_error?({:no_instance, _interface, _head}), do: true
  defp structured_error?({:no_named_instance, _name}), do: true
  defp structured_error?({:overlapping_instance, _interface, _head}), do: true
  defp structured_error?({:overlapping_named_instance, _name, _interface, _head}), do: true
  defp structured_error?({:unsupported_pattern, _shape}), do: true

  defp structured_error?({kind, _name})
       when kind in [:unknown_ctor, :foreign_ctor, :unknown_pattern_constructor, :unknown_family],
       do: true

  defp structured_error?({:lift_module_error, details}) when is_map(details), do: true
  defp structured_error?({:conversion_failure, _actual, _expected}), do: true
  defp structured_error?({:codegen_error, {:conversion_failure, _actual, _expected}}), do: true

  defp structured_error?({kind, _, _})
       when kind in [:unbound_variable, :arity_mismatch, :ambiguous_name, :duplicate_module],
       do: true

  defp structured_error?({:import_cycle, _hops}), do: true
  defp structured_error?({:unresolved_import, _, _, _, _}), do: true
  defp structured_error?({:unexpected_token, _, _, _}), do: true
  defp structured_error?({:expected_token, _, _, _, _, _}), do: true
  defp structured_error?({:expected, _, :got, _, _, _}), do: true
  defp structured_error?({:parse_recovered, _, _, _}), do: true
  defp structured_error?({:lambda_block_unterminated, _, _, _}), do: true
  defp structured_error?({:lex_error, _reason}), do: true
  defp structured_error?({:missing_diagnosis, _points}), do: true
  defp structured_error?({:rule_unpinned, _keywords}), do: true
  defp structured_error?({:example_mismatch, _mismatches}), do: true
  defp structured_error?({:example_type_mismatch, _failures}), do: true
  defp structured_error?({:computed_example_error, _failures}), do: true
  defp structured_error?({:computed_macro_error, meta, _reason}) when is_list(meta), do: true
  defp structured_error?({:macro_expansion_cycle, chain}) when is_list(chain), do: true

  defp structured_error?({:macro_expansion_budget, kind, frames})
       when is_atom(kind) and is_list(frames),
       do: true

  defp structured_error?({:expansion_ill_typed, details}) when is_map(details), do: true
  defp structured_error?({:macro_use_mismatch, _keyword, _expected, _got, _line, _column}), do: true
  defp structured_error?({:malformed_hole, _line, _column}), do: true
  defp structured_error?({:file_read_error, _path, _reason}), do: true
  defp structured_error?({:file_write_error, _path, _reason}), do: true
  defp structured_error?({:dependency_resolution_failed, _reason}), do: true
  defp structured_error?({:command_failed, _command, _reason}), do: true
  defp structured_error?({:migration_warning, details}) when is_map(details), do: true
  defp structured_error?({:compiler_warning, details}) when is_map(details), do: true
  defp structured_error?({:export_unmappable, _reason}), do: true
  defp structured_error?({:snap_missing, _path}), do: true
  defp structured_error?({:configuration_warning, _message}), do: true
  defp structured_error?({:usage_error, _message}), do: true
  defp structured_error?({:artifact_error, _message}), do: true
  defp structured_error?({:proof_file_missing, _detail}), do: true
  defp structured_error?({:proof_verification_failed, _detail}), do: true
  defp structured_error?({:proof_schema_incompatible, _detail}), do: true
  defp structured_error?({:snap_schema_incompatible, _detail}), do: true
  defp structured_error?({:registry_signature_invalid, _detail}), do: true
  defp structured_error?({:transparency_log_unreachable, _detail}), do: true
  defp structured_error?({:registry_fetch_failed, _detail}), do: true
  defp structured_error?({:registry_hash_mismatch, _detail}), do: true
  defp structured_error?({:registry_package_not_found, _detail}), do: true
  defp structured_error?({:version_conflict, _name, _constraints}), do: true
  defp structured_error?({:undocumented_public_function, _file, _line}), do: true
  defp structured_error?({:beam_lint_error, _errors, _warnings}), do: true
  defp structured_error?({:beam_lint_error, _errors}), do: true
  defp structured_error?({:final_core_violation, rejections}) when is_list(rejections), do: true
  defp structured_error?({:final_core_violation, _name, rejections}) when is_list(rejections), do: true
  defp structured_error?({:expected_module, _ast}), do: true
  defp structured_error?({:unsupported_container, _type}), do: true
  defp structured_error?({:edition_error, {:unknown_edition, _edition}}), do: true

  defp structured_error?({kind, _, _})
       when kind in [:edition_pragma_placement, :edition_pragma_malformed, :edition_pragma_unknown], do: true

  defp structured_error?({:codegen_error, _reason}), do: true
  defp structured_error?({:parse_error, [reason | _]}), do: structured_error?(reason)
  defp structured_error?({:source_context, reason, context}) when is_map(context), do: structured_error?(reason)
  defp structured_error?([reason | _]), do: structured_error?(reason)
  defp structured_error?([]), do: true
  defp structured_error?(_error), do: false

  defp operational_error?({:file_read_error, _, _}), do: true
  defp operational_error?({:file_write_error, _, _}), do: true
  defp operational_error?({:dependency_resolution_failed, _}), do: true
  defp operational_error?({:command_failed, _, _}), do: true
  defp operational_error?({:migration_warning, details}) when is_map(details), do: true
  defp operational_error?({:compiler_warning, details}) when is_map(details), do: true
  defp operational_error?({:export_unmappable, _}), do: true
  defp operational_error?({:snap_missing, _}), do: true
  defp operational_error?({:configuration_warning, _}), do: true
  defp operational_error?({:usage_error, _}), do: true
  defp operational_error?({:artifact_error, _}), do: true
  defp operational_error?({:proof_file_missing, _}), do: true
  defp operational_error?({:proof_verification_failed, _}), do: true
  defp operational_error?({:proof_schema_incompatible, _}), do: true
  defp operational_error?({:snap_schema_incompatible, _}), do: true
  defp operational_error?({:registry_signature_invalid, _}), do: true
  defp operational_error?({:transparency_log_unreachable, _}), do: true
  defp operational_error?({:registry_fetch_failed, _}), do: true
  defp operational_error?({:registry_hash_mismatch, _}), do: true
  defp operational_error?({:registry_package_not_found, _}), do: true
  defp operational_error?({:version_conflict, _, _}), do: true
  defp operational_error?({:invalid_dependency, _}), do: true
  defp operational_error?({:invalid_constraint, _, _}), do: true
  defp operational_error?({:no_versions, _}), do: true
  defp operational_error?({:dependency_clone_failed, _, _}), do: true
  defp operational_error?({:dependency_edition_error, _, _}), do: true
  defp operational_error?({:duplicate_app, _}), do: true
  defp operational_error?({:app_name_mismatch, _, _}), do: true
  defp operational_error?({:compile_failed, _}), do: true
  defp operational_error?({:release_build_failed, _}), do: true
  defp operational_error?({:release_app_missing, _, _}), do: true
  defp operational_error?({:sys_config_read_failed, _, _}), do: true
  defp operational_error?({:vm_args_read_failed, _, _}), do: true
  defp operational_error?({:undocumented_public_function, _, _}), do: true
  defp operational_error?(_), do: false

  defp error_location({:lift_module_error, %{source_provenance: %{line: line, col: col}}}), do: {line, col}
  defp error_location({:unresolved_import, _name, _arity, _imports, line}) when is_integer(line), do: {line, 1}
  defp error_location({:import_cycle, [%{line: line} | _]}) when is_integer(line), do: {line, 1}
  defp error_location({:duplicate_module, _name, _paths}), do: {1, 1}
  defp error_location({:ambiguous_name, _name, _modules}), do: {1, 1}
  defp error_location({:lambda_block_unterminated, line, col, _code}), do: {line, col}
  defp error_location({:lex_error, reason}), do: lex_error_location(reason)
  defp error_location({_, _, meta}) when is_list(meta), do: {Keyword.get(meta, :line, 0), Keyword.get(meta, :col, 0)}
  defp error_location({_, _, line, col}) when is_integer(line) and is_integer(col), do: {line, col}

  defp error_location({:expected, _expected, :got, _actual, line, col})
       when is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location({:expected_token, _expected, _actual_type, _actual_value, line, col})
       when is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location({:macro_use_mismatch, _keyword, _expected, _got, line, col})
       when is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location({:malformed_hole, line, col})
       when is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location({:computed_macro_error, meta, _reason}) when is_list(meta) do
    {Keyword.get(meta, :line, 0), Keyword.get(meta, :col, Keyword.get(meta, :column, 0))}
  end

  defp error_location({kind, line, col})
       when kind in [:edition_pragma_placement, :edition_pragma_malformed, :edition_pragma_unknown] and
              is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location({:parse_error, [reason | _]}), do: error_location(reason)
  defp error_location({:codegen_error, reason}), do: error_location(reason)

  defp error_location({:source_context, _reason, %{line: line, column: col}})
       when is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location(_error), do: {0, 0}

  defp exact_error_span(error, source, source_id, registry) do
    case hole_span(error, source) do
      {:ok, start_byte, end_byte} ->
        Cure.Diagnostic.SourceRegistry.span(registry, source_id, start_byte, end_byte)

      :error ->
        exact_error_span_without_hole(error, source, source_id, registry)
    end
  end

  defp exact_error_span_without_hole(error, source, source_id, registry) do
    if insertion_at_eof?(error) do
      ending = byte_size(source)
      Cure.Diagnostic.SourceRegistry.span(registry, source_id, ending, ending)
    else
      case embedded_span(error) do
        %Cure.Diagnostic.Span{} = span ->
          Cure.Diagnostic.SourceRegistry.span(registry, source_id, span.start_byte, span.end_byte)

        nil ->
          token_span_at_error(error, source, source_id, registry)
      end
    end
  end

  defp hole_span({:codegen_error, reason}, source), do: hole_span(reason, source)

  defp hole_span({:unfilled_hole, _name}, source) do
    case Regex.run(~r/\?{3}|\?{1,2}[A-Za-z_][A-Za-z0-9_]*/, source, return: :index) do
      [{start_byte, length}] -> {:ok, start_byte, start_byte + length}
      _ -> :error
    end
  end

  defp hole_span(_error, _source), do: :error

  defp insertion_at_eof?({:lex_error, {kind, _line, _column}})
       when kind in [:unterminated_string, :unterminated_char, :unterminated_quoted_identifier],
       do: true

  defp insertion_at_eof?({:parse_error, [reason | _]}), do: insertion_at_eof?(reason)
  defp insertion_at_eof?(_error), do: false

  defp token_span_at_error(error, source, source_id, registry) do
    case error_location(error) do
      {line, col} when line > 0 and col > 0 ->
        token =
          with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: "diagnostic", emit_events: false) do
            Enum.find(tokens, fn
              %Cure.Compiler.Token{span: %Cure.Diagnostic.Span{} = span} ->
                span.start_line == line and span.start_column == col

              _ ->
                false
            end)
          else
            _ -> nil
          end

        case token do
          %Cure.Compiler.Token{span: %Cure.Diagnostic.Span{} = span} ->
            Cure.Diagnostic.SourceRegistry.span(registry, source_id, span.start_byte, span.end_byte)

          nil ->
            case Cure.Diagnostic.SourceRegistry.span_at(registry, source_id, line, col, 0) do
              {:ok, span} -> {:ok, span}
              {:error, _} -> :error
            end
        end

      _ ->
        :error
    end
  end

  defp embedded_span({:parse_error, [reason | _]}), do: embedded_span(reason)
  defp embedded_span({:codegen_error, reason}), do: embedded_span(reason)
  defp embedded_span({:source_context, _reason, %{span: %Cure.Diagnostic.Span{} = span}}), do: span
  defp embedded_span(_error), do: nil

  defp lex_error_location(reason) when is_tuple(reason) do
    case reason |> Tuple.to_list() |> Enum.reverse() do
      [col, line | _] when is_integer(line) and is_integer(col) -> {line, col}
      _ -> {0, 0}
    end
  end

  defp lex_error_location(_reason), do: {0, 0}

  defp extract_line({_, _, meta}) when is_list(meta), do: Keyword.get(meta, :line, 0)
  defp extract_line({_, _, line, _col}) when is_integer(line), do: line
  defp extract_line(_), do: 0

  defp extract_col({_, _, _line, col}) when is_integer(col), do: col
  defp extract_col(_), do: 0

  # Levenshtein distance for typo suggestions
  defp levenshtein(s, t) do
    s_len = String.length(s)
    t_len = String.length(t)
    s_chars = String.graphemes(s)
    t_chars = String.graphemes(t)

    if s_len == 0 do
      t_len
    else
      if t_len == 0 do
        s_len
      else
        prev_row = Enum.to_list(0..t_len)

        Enum.reduce(Enum.with_index(s_chars, 1), prev_row, fn {s_ch, i}, row ->
          first = [i]

          rest =
            Enum.reduce(Enum.with_index(t_chars, 1), {first, row}, fn {t_ch, j}, {new_row, old_row} ->
              cost = if s_ch == t_ch, do: 0, else: 1

              val =
                Enum.min([
                  Enum.at(old_row, j) + 1,
                  List.last(new_row) + 1,
                  Enum.at(old_row, j - 1) + cost
                ])

              {new_row ++ [val], old_row}
            end)

          elem(rest, 0)
        end)
        |> List.last()
      end
    end
  end
end
