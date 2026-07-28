defmodule Cure.Diagnostic.Adapter.Codegen do
  @moduledoc """
  Converts failures from the trusted Core/BEAM emission boundary.

  Ordinary source failures must be converted before they reach this module.
  Every diagnostic produced here is therefore E101 and carries enough stable
  context to report the compiler defect without exposing a stacktrace.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error({:codegen_failure, details}, opts) when is_map(details) do
    opts =
      opts
      |> Keyword.put(:codegen_stage, Map.get(details, :stage))
      |> Keyword.put(:codegen_module, Map.get(details, :module))
      |> Keyword.put(:source_file, Map.get(details, :file, Keyword.get(opts, :source_file)))

    failure(Map.get(details, :reason), opts)
  end

  def from_error({:codegen_error, reason}, opts), do: failure(reason, opts)
  def from_error({:beam_lint_error, errors, warnings}, opts), do: failure({:beam_lint, errors, warnings}, opts)
  def from_error({:beam_lint_error, errors}, opts), do: failure({:beam_lint, errors}, opts)
  def from_error({:final_core_violation, rejections}, opts), do: final_core(nil, rejections, opts)
  def from_error({:final_core_violation, name, rejections}, opts), do: final_core(name, rejections, opts)
  def from_error({:expected_module, _ast}, opts), do: failure(:expected_module, opts)
  def from_error({:unsupported_container, type}, opts), do: failure({:unsupported_container, type}, opts)
  def from_error({:cannot_emit, reason}, opts), do: failure({:cannot_emit, reason}, opts)

  defp failure(reason, opts) do
    {title, body, kind} = failure_content(reason)
    stage = Keyword.get(opts, :codegen_stage) || stage(reason)
    module = Keyword.get(opts, :codegen_module)
    file = source_file(opts)
    reason_text = reason_text(reason)
    fingerprint = fingerprint({stage, module, file, reason})

    context =
      [
        "Stage: `#{name(stage)}`.",
        if(module, do: "Module: `#{name(module)}`."),
        if(file, do: "Source: `#{file}`."),
        "Underlying reason: #{reason_text}.",
        "Diagnostic fingerprint: `#{fingerprint}`."
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" ")

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: title,
      body: Doc.stack([Doc.paragraph(body), Doc.paragraph(context)]),
      primary: primary(opts, "code generation failed here"),
      notes: ["This is an internal compiler failure; report it with the diagnostic fingerprint."],
      payload: %{
        kind: kind,
        stage: stage,
        module: module,
        file: file,
        reason: reason_text,
        fingerprint: fingerprint
      }
    )
  end

  defp final_core(name, rejections, opts) when is_list(rejections) do
    clauses = Enum.map(rejections, &Map.get(&1, :clause))
    messages = Enum.map(rejections, &Map.get(&1, :message))
    stage = Keyword.get(opts, :codegen_stage, :final_core_validation)
    module = Keyword.get(opts, :codegen_module)
    file = source_file(opts)
    fingerprint = fingerprint({stage, module, file, name, rejections})

    context =
      [
        "Stage: `#{name(stage)}`.",
        if(module, do: "Module: `#{name(module)}`."),
        if(file, do: "Source: `#{file}`."),
        "Diagnostic fingerprint: `#{fingerprint}`."
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" ")

    Diagnostic.new(
      code: "E101",
      key: :internal_compiler_error,
      severity: :error,
      title: "Final-Core validation failed",
      body:
        Doc.stack([
          Doc.paragraph(
            "The compiler rejected an internal Core term at the trusted boundary (#{Enum.join(Enum.map(messages, &to_string/1), "; ")})."
          ),
          Doc.paragraph(context)
        ]),
      primary: primary(opts, "this definition produced invalid internal Core"),
      notes: ["This is an internal compiler failure; report it with the diagnostic fingerprint."],
      payload: %{
        kind: :final_core_violation,
        name: name,
        clauses: clauses,
        messages: messages,
        stage: stage,
        module: module,
        file: file,
        fingerprint: fingerprint
      }
    )
  end

  defp stage({:beam_lint, _errors}), do: :beam_writer
  defp stage({:beam_lint, _errors, _warnings}), do: :beam_writer
  defp stage({:missing_stdlib_module, _module, _message}), do: :module_resolution
  defp stage(_reason), do: :codegen

  defp failure_content(:expected_module) do
    {"Module emission failed", "The compiler expected a module definition before emitting a BEAM artifact.",
     :expected_module}
  end

  defp failure_content({:unsupported_container, type}) do
    {"Unsupported container", "The compiler cannot emit the `#{name(type)}` container in this context.",
     :unsupported_container}
  end

  defp failure_content({:beam_lint, errors, warnings}) when is_list(errors) and is_list(warnings) do
    {"BEAM validation failed",
     "The generated BEAM artifact was rejected by the BEAM validator (#{length(errors)} error(s), #{length(warnings)} warning(s)).",
     :beam_lint}
  end

  defp failure_content({:beam_lint, errors}) when is_list(errors) do
    {"BEAM validation failed",
     "The generated BEAM artifact was rejected by the BEAM validator (#{length(errors)} error(s)).", :beam_lint}
  end

  defp failure_content({:missing_stdlib_module, module, message}) do
    {"Stdlib module resolution failed",
     "The compiler could not resolve `#{name(module)}` while generating the BEAM artifact. #{message}",
     :missing_stdlib_module}
  end

  defp failure_content(_reason) do
    {"Code generation failed", "The compiler could not produce a valid BEAM artifact for this source.", :codegen}
  end

  defp reason_text({:beam_lint, errors}), do: beam_diagnostics(errors)

  defp reason_text({:beam_lint, errors, warnings}) do
    errors_text = beam_diagnostics(errors)
    warnings_text = beam_diagnostics(warnings)
    if warnings_text == "no details", do: errors_text, else: errors_text <> "; warnings: " <> warnings_text
  end

  defp reason_text({:compilation_failed, errors}), do: beam_diagnostics(errors)
  defp reason_text(reason), do: human_reason(reason)

  defp beam_diagnostics(diagnostics) do
    diagnostics
    |> List.wrap()
    |> Enum.flat_map(fn
      {_file, entries} when is_list(entries) -> entries
      entry -> [entry]
    end)
    |> Enum.take(3)
    |> Enum.map_join("; ", &beam_diagnostic/1)
    |> case do
      "" -> "no details"
      text -> text
    end
  end

  defp beam_diagnostic({location, formatter, detail}) when is_atom(formatter) do
    message =
      try do
        formatter.format_error(detail) |> IO.iodata_to_binary() |> String.trim()
      rescue
        _ -> human_reason(detail)
      end

    "#{human_reason(location)}: #{message}"
  end

  defp beam_diagnostic(other), do: human_reason(other)

  defp human_reason(value) when is_binary(value), do: value
  defp human_reason(value) when is_atom(value), do: Atom.to_string(value)
  defp human_reason(value) when is_number(value), do: to_string(value)
  defp human_reason(value) when is_list(value), do: value |> Enum.take(3) |> Enum.map_join(", ", &human_reason/1)

  defp human_reason(value) when is_tuple(value) do
    value |> Tuple.to_list() |> Enum.take(4) |> Enum.map_join(": ", &human_reason/1)
  end

  defp human_reason(%_{} = value), do: value |> Map.from_struct() |> human_reason()

  defp human_reason(value) when is_map(value) do
    value
    |> Enum.sort_by(fn {key, _value} -> to_string(key) end)
    |> Enum.take(4)
    |> Enum.map_join(", ", fn {key, nested} -> "#{key}=#{human_reason(nested)}" end)
  end

  defp human_reason(value), do: inspect(value, limit: 4, printable_limit: 120)

  defp source_file(opts) do
    Keyword.get(opts, :source_file) ||
      case Keyword.get(opts, :span) do
        %Span{path: path} -> path
        _ -> nil
      end
  end

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      nil -> nil
    end
  end

  defp fingerprint(term) do
    term
    |> :erlang.term_to_binary()
    |> then(&:crypto.hash(:sha256, &1))
    |> Base.encode16(case: :lower)
    |> binary_part(0, 12)
  end

  defp name(value) when is_atom(value), do: Atom.to_string(value)
  defp name(value) when is_binary(value), do: value
  defp name(value), do: inspect(value)
end
