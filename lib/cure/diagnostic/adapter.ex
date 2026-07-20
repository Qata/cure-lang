defmodule Cure.Diagnostic.Adapter do
  @moduledoc "Converts phase-specific and legacy error values into shared diagnostics."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Label, ProvenanceFrame, Span, Suggestion}

  @unknown_name_code "E091"

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:error, reason}, opts), do: from_error(reason, opts)

  def from_error({:unknown_global, name}, opts),
    do: unknown_name(:value, name, opts)

  def from_error({:unknown_constructor, name}, opts),
    do: unknown_name(:constructor, name, opts)

  def from_error({:unknown_type, name}, opts),
    do: unknown_name(:type, name, opts)

  def from_error({:unknown_module, name}, opts),
    do: unknown_name(:module, name, opts)

  def from_error({:unknown_member, module, name}, opts),
    do: unknown_name(:member, "#{module}.#{name}", Keyword.put(opts, :owner, module))

  def from_error({:lift_module_error, details}, opts) when is_map(details) do
    macro = get_in(details, [:source_provenance, :macro]) || :macro
    cause = Map.get(details, :cause)
    cause_diagnostic = from_error(cause)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "#{macro_title(macro)} expansion failed",
      message: macro_failure_message(macro, details.module, cause_diagnostic),
      primary: primary_label(opts, "this `#{macro}` declaration generated the failing module"),
      notes: ["The generated module is an implementation detail; edit the `#{macro}` declaration instead."],
      provenance: provenance_frames(details, opts),
      payload: %{
        macro: name_to_string(macro),
        module: name_to_string(details.module),
        behaviour: Map.get(details, :behaviour),
        cause: %{code: cause_diagnostic.code, key: cause_diagnostic.key, payload: cause_diagnostic.payload}
      }
    )
  end

  def from_error(error, opts) do
    key = Diagnostic.key(error) || :compilation_error

    Diagnostic.new(
      code: Keyword.get(opts, :code, "E000"),
      key: key,
      severity: Keyword.get(opts, :severity, :error),
      title: Keyword.get(opts, :title, "Compilation error"),
      message: Keyword.get(opts, :message, "The compiler rejected this program."),
      primary: primary_label(opts),
      notes: Keyword.get(opts, :notes, []),
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{legacy_reason: inspect(error)}
    )
  end

  @spec unknown_name(atom(), term(), keyword()) :: Diagnostic.t()
  def unknown_name(namespace, name, opts \\ []) do
    spelling = name_to_string(name)
    candidates = opts |> Keyword.get(:candidates, []) |> Enum.map(&name_to_string/1) |> Enum.uniq()

    Diagnostic.new(
      code: @unknown_name_code,
      key: :unknown_name,
      severity: :error,
      title: "Unknown #{namespace_title(namespace)}",
      message: "`#{spelling}` is not available in this #{namespace} namespace.",
      primary: primary_label(opts, "`#{spelling}` was not found"),
      notes: Keyword.get(opts, :notes, []),
      suggestions: candidate_suggestions(candidates),
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        namespace: namespace,
        name: spelling,
        candidates: candidates,
        owner: Keyword.get(opts, :owner),
        checking: Keyword.get(opts, :checking)
      }
    )
  end

  defp primary_label(opts, default_message \\ nil) do
    case Keyword.get(opts, :span) do
      %Span{} = span ->
        %Label{
          span: span,
          style: :primary,
          message: Keyword.get(opts, :label, default_message)
        }

      nil ->
        nil
    end
  end

  defp candidate_suggestions([]), do: []

  defp candidate_suggestions(candidates) do
    [
      %Suggestion{
        message: "Did you mean #{Enum.map_join(candidates, ", ", &"`#{&1}`")}?",
        applicability: :maybe_incorrect
      }
    ]
  end

  defp namespace_title(:value), do: "value"
  defp namespace_title(:constructor), do: "constructor"
  defp namespace_title(:type), do: "type"
  defp namespace_title(:module), do: "module"
  defp namespace_title(:member), do: "module member"
  defp namespace_title(other), do: to_string(other)

  defp macro_title(macro), do: macro |> name_to_string() |> String.capitalize()

  defp macro_failure_message(macro, module, %Diagnostic{} = cause) do
    "The `#{macro}` declaration could not generate `#{module}`. #{cause.message}"
  end

  defp provenance_frames(details, opts) do
    source = Map.get(details, :source_provenance) || %{}
    chain = Map.get(details, :expansion_provenance, [])
    invocation = Keyword.get(opts, :span)

    frames =
      Enum.map(chain, fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword) || "macro",
          invocation: invocation
        }
      end)

    source_frame =
      case Map.get(source, :macro) do
        nil -> []
        macro -> [%ProvenanceFrame{kind: :macro_expansion, name: macro, invocation: invocation}]
      end

    (frames ++ source_frame)
    |> Enum.uniq_by(& &1.name)
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
