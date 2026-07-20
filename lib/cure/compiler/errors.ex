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

  def format_error(%Cure.Diagnostic{} = diagnostic, _file) do
    Cure.Diagnostic.Renderer.plain(diagnostic)
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
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "type mismatch", file, line, message)
  end

  def format_error({:unknown_erasure_class, name, class}, file) do
    format_diagnostic(
      "error",
      "unknown erasure class",
      file,
      0,
      "`@erases(#{inspect(class)})` on `#{name}` is not a known erasure class; " <>
        "known classes: #{known_erasure_classes_hint()}"
    )
  end

  def format_error({:erases_on_non_opaque, name}, file) do
    format_diagnostic(
      "error",
      "@erases on a non-opaque type",
      file,
      0,
      "`#{name}` has constructors, so its erasure is already determined; `@erases` " <>
        "declares the runtime shape of a CONSTRUCTOR-LESS carrier (`opaque type`)"
    )
  end

  def format_error({:unsupported_async, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "unsupported asynchronous primitive", file, line, message)
  end

  def format_error({:splice_outside_quote, tag, meta}, file) do
    line = Keyword.get(meta, :line, 0)

    form = if tag == :splice_group, do: "$(e ...)", else: "$(e)"

    format_diagnostic(
      "error",
      "splice outside quote",
      file,
      line,
      "a #{form} splice is only meaningful inside a `quote`; there is no quoted form here to splice into"
    )
  end

  def format_error({:extern_untyped_head, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "@extern declaration missing a typed head (E056)", file, line, message)
  end

  def format_error({:extern_has_body, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "@extern declaration has a body (E057)", file, line, message)
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

  def format_error({:lambda_block_unterminated, _, _, _} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  # -- Lex Errors --------------------------------------------------------------

  def format_error({:lex_error, _reason} = error, file),
    do: error |> Cure.Diagnostic.Adapter.from_error() |> format_error(file)

  # -- Codegen Errors ----------------------------------------------------------

  def format_error({:codegen_error, {:computed_macro_error, _meta, _reason} = error}, file),
    do: format_error(error, file)

  def format_error({:codegen_error, reason}, file) do
    format_diagnostic("error", "codegen error", file, 0, inspect(reason))
  end

  def format_error({:beam_lint_error, errors, warnings}, file) do
    warned = Enum.map_join(warnings, "\n", &format_error(&1, file))
    warned <> "\n" <> format_error({:beam_lint_error, errors}, file)
  end

  def format_error({:beam_lint_error, errors}, file) do
    # erl_lint errors come as `[{file_info, [{line, module, payload}, ...]}]`.
    lines =
      errors
      |> Enum.flat_map(fn
        {_file_info, entries} when is_list(entries) -> entries
        other -> [other]
      end)
      |> Enum.map(fn
        {line, :erl_lint, {:undefined_function, {fn_name, arity}}} ->
          "line #{line}: undefined function #{fn_name}/#{arity}"

        {line, module, payload} ->
          "line #{line}: #{module}: #{inspect(payload)}"

        other ->
          raise Cure.Diagnostic.UnhandledError, error: {:beam_lint_entry, other}
      end)

    format_diagnostic("error", "BEAM lint error", file, 0, Enum.join(lines, "\n      | "))
  end

  def format_error({:expected_module, _ast}, file) do
    format_diagnostic("error", "codegen error", file, 0, "expected a module definition")
  end

  def format_error({:unsupported_container, type}, file) do
    format_diagnostic("error", "codegen error", file, 0, "unsupported container type: #{type}")
  end

  # -- File Errors -------------------------------------------------------------

  def format_error({:file_read_error, path, reason}, _file) do
    format_diagnostic("error", "file error", path, 0, "cannot read file: #{:file.format_error(reason)}")
  end

  # -- DepGraph / Build-Order Errors -------------------------------------------

  # -- Edition Errors ----------------------------------------------------------

  def format_error({:edition_pragma_placement, line, col}, file) do
    format_diagnostic(
      "error",
      "misplaced edition pragma",
      file,
      line,
      "the `@edition(\"YYYY\")` pragma must be the first thing in the file, " <>
        "before any statement or decorated definition (column #{col})"
    )
  end

  def format_error({:edition_pragma_malformed, line, col}, file) do
    format_diagnostic(
      "error",
      "malformed edition pragma",
      file,
      line,
      "the `@edition` argument must be a single 4-digit year string on one line, " <>
        "e.g. `@edition(\"#{Cure.Edition.current()}\")` (column #{col})"
    )
  end

  def format_error({:edition_pragma_unknown, line, col}, file) do
    format_diagnostic(
      "error",
      "unknown edition",
      file,
      line,
      "not a known edition (column #{col}); known editions: #{known_editions_hint()}"
    )
  end

  def format_error({:edition_error, {:unknown_edition, edition}}, file) do
    format_diagnostic(
      "error",
      "unknown edition",
      file,
      0,
      "#{inspect(edition)} is not a known edition; known editions: #{known_editions_hint()}"
    )
  end

  # -- Macro error floor (SP1 §2) ----------------------------------------------

  def format_error({:macro_use_mismatch, keyword, expected, got, line, col}, file) do
    detail =
      case expected do
        {:literal, w} -> "the `#{keyword}` macro expected `#{w}` here, but found `#{got}`"
        {:hole_kind, k} -> "the `#{keyword}` macro expected #{article(k)} #{k} here, but found `#{got}`"
        :nothing_more -> "the `#{keyword}` macro has no more to match here, but found `#{got}`"
      end

    format_diagnostic("error", "macro syntax", file, line, "#{detail} (at column #{col})")
  end

  def format_error({:malformed_hole, line, col}, file) do
    format_diagnostic(
      "error",
      "macro syntax",
      file,
      line,
      "malformed hole at column #{col} — a macro hole is written `<name: Kind>` " <>
        "(e.g. `<period: Duration>`); check for a missing `:` or closing `>`"
    )
  end

  def format_error({:missing_diagnosis, points}, file) do
    listed = points |> Enum.map(&describe_point/1) |> Enum.join(", ")

    format_diagnostic(
      "error",
      "macro is missing a failure description",
      file,
      0,
      "this macro can fail in ways it does not describe: #{listed}. Add an `explain` " <>
        "clause for each (a `Category =>` covers a typed hole, `keyword \"w\" =>` a literal)."
    )
  end

  def format_error({:rule_unpinned, keywords}, file) do
    listed = keywords |> Enum.map(&"`#{&1}`") |> Enum.join(", ")

    format_diagnostic(
      "error",
      "macro rule has no worked example",
      file,
      0,
      "these rules are not pinned by an example: #{listed}. Add an indented " <>
        "`example <use> expands <result>` under each rule so its intent is checked, not just its type."
    )
  end

  def format_error({:example_mismatch, mismatches}, file) do
    listed = mismatches |> Enum.map(&"`#{&1.keyword}`") |> Enum.join(", ")

    format_diagnostic(
      "error",
      "macro example does not match its expansion",
      file,
      0,
      "these rules have an `example … expands …` whose stated result is not what the rule " <>
        "actually produces: #{listed}. Fix the `expands` side to the real expansion (or the rule)."
    )
  end

  def format_error({:example_type_mismatch, failures}, file) do
    listed =
      failures
      |> Enum.map_join(", ", fn failure ->
        "`#{failure.keyword}` (expected #{inspect(failure.expected)}, got #{inspect(failure.reason)})"
      end)

    format_diagnostic(
      "error",
      "macro example has the wrong type",
      file,
      0,
      "these rules have a type-only example pin that their expansion does not satisfy: #{listed}"
    )
  end

  def format_error({:computed_example_error, failures}, file) do
    listed =
      failures
      |> Enum.map_join(", ", fn failure ->
        "`#{failure.keyword}` (#{inspect(failure.reason)})"
      end)

    format_diagnostic(
      "error",
      "computed macro example failed",
      file,
      0,
      "these computed rules could not execute their pinned examples: #{listed}"
    )
  end

  def format_error({:computed_macro_error, meta, reason}, file) do
    line = Keyword.get(meta, :line, 0)
    keyword = Keyword.get(meta, :keyword, "computed")

    {title, detail} = format_generated_syntax_reason(reason)

    format_diagnostic(
      "error",
      title,
      file,
      line,
      "the `#{keyword}` computed macro could not produce a valid Syntax expansion: #{detail}"
    )
  end

  def format_error({:expansion_ill_typed, details}, file) do
    keyword = Map.get(details, :keyword, "?")
    reason = Map.get(details, :kernel_error)

    format_diagnostic(
      "error",
      "macro expansion proof failed",
      file,
      0,
      "the generated `#{keyword}` expansion was rejected by the dependent elaborator: #{inspect(reason)}"
    )
  end

  # -- Exhaustiveness guard ----------------------------------------------------

  def format_error(error, file) do
    raise Cure.Diagnostic.UnhandledError, error: %{error: error, file: file}
  end

  defp format_generated_syntax_reason({:invalid_generated_syntax, {:raw_syntax_in_expansion, path}}),
    do:
      {"invalid macro expansion",
       "raw syntax is only valid for reflection, not generated Cure code (#{format_syntax_path(path)})"}

  defp format_generated_syntax_reason({:invalid_generated_syntax, {:quoted_syntax_in_expansion, path}}),
    do:
      {"invalid macro expansion",
       "quoted syntax must be unquoted before it is emitted as Cure code (#{format_syntax_path(path)})"}

  defp format_generated_syntax_reason({:invalid_generated_syntax, {reason, path}}),
    do: {"invalid macro expansion", "#{inspect(reason)} (#{format_syntax_path(path)})"}

  defp format_generated_syntax_reason({:author_diagnostics, diagnostics}) when is_list(diagnostics),
    do: {"macro rejected expansion", format_author_diagnostics(diagnostics)}

  defp format_generated_syntax_reason({:author_failure, name, args}) when is_list(args),
    do: {"macro rejected expansion", "the macro reported `#{name}`#{format_author_args(args)}"}

  defp format_generated_syntax_reason(reason), do: {"computed macro failed", inspect(reason)}

  defp format_author_diagnostics([]), do: "the macro returned no diagnostic details"

  defp format_author_diagnostics(diagnostics) do
    details = Enum.map_join(diagnostics, "; ", &inspect/1)
    "the macro reported #{length(diagnostics)} diagnostic(s): #{details}"
  end

  defp format_author_args([]), do: ""
  defp format_author_args(args), do: ": #{Enum.map_join(args, ", ", &inspect/1)}"

  defp format_syntax_path(path) do
    path
    |> Enum.reverse()
    |> Enum.map_join(".", fn
      {:child, index} -> "child[#{index}]"
      {:attribute, key, index} -> "attribute #{key}[#{index}]"
      {:syntax_literal} -> "syntax literal"
      {:map_key} -> "map key"
      {:map_value} -> "map value"
      {:list_item} -> "list item"
      other -> raise Cure.Diagnostic.UnhandledError, error: {:syntax_path_segment, other}
    end)
  end

  defp known_editions_hint, do: Enum.join(Cure.Edition.all(), ", ")

  defp known_erasure_classes_hint,
    do: Cure.Elab.Declarations.erasure_classes() |> Enum.map_join(", ", &to_string/1)

  defp describe_point({:hole_kind, k}), do: "a `#{k}` hole"
  defp describe_point({:keyword, w}), do: "the keyword `#{w}`"
  defp describe_point({:failure, name}), do: "the author failure `#{name}`"

  # Grammatical article for the macro hole-kind diagnostic ("a Duration" / "an
  # Int"). Placed after the format_error/2 clause group to keep those contiguous.
  defp article(<<c, _::binary>>) when c in ~c"AEIOUaeiou", do: "an"
  defp article(_), do: "a"

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
  defp structured_error?({:unsupported_async, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:splice_outside_quote, _tag, meta}) when is_list(meta), do: true
  defp structured_error?({:unbound_variable, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:arity_mismatch, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:extern_untyped_head, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:extern_has_body, _message, meta}) when is_list(meta), do: true
  defp structured_error?({:unknown_record, _name}), do: true
  defp structured_error?({:record_field_mismatch, _name}), do: true
  defp structured_error?({:unknown_type, _name}), do: true
  defp structured_error?({:unknown_module, _name}), do: true
  defp structured_error?({:unknown_member, _module, _name}), do: true
  defp structured_error?({:proof_shape_mismatch, _message, _name}), do: true
  defp structured_error?({:totality_required, _name}), do: true
  defp structured_error?({:compile_time_totality, _name, _reason}), do: true

  defp structured_error?({kind, _message, meta})
       when kind in [:pickup_no_else, :pickup_else_not_last, :pickup_multiple_else] and is_list(meta),
       do: true

  defp structured_error?({:duplicate_module_identity, _name, _other_path, _path}), do: true
  defp structured_error?({:duplicate_module_identity, _name, paths}) when is_list(paths), do: true
  defp structured_error?({:unfilled_hole, _name}), do: true
  defp structured_error?({:unsolved_metavariables, _name}), do: true
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

  # -- Formatting Helper -------------------------------------------------------

  defp format_diagnostic(severity, category, file, line, message) do
    location =
      cond do
        line > 0 ->
          " --> " <> Cure.Term.Hyperlink.file_line_link(file, line)

        file in ["", "nofile", nil] ->
          " --> #{file}"

        true ->
          " --> " <> Cure.Term.Hyperlink.file_link(file)
      end

    """
    #{severity}: #{category}
    #{location}
      | #{message}\
    """
    |> String.trim_trailing()
  end

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
