defmodule Cure.Diagnostic.Adapter.Name do
  @moduledoc """
  Converts unresolved-name failures and owns deterministic candidate repairs.

  Candidate maps retain semantic identity, owner, namespace, visibility,
  qualification/import requirements, arity, and origin in the machine payload.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion, TextEdit}
  alias Cure.Diagnostic.Suggest

  @spec unknown_name(atom(), term(), keyword()) :: Diagnostic.t()
  def unknown_name(namespace, name, opts \\ []) do
    spelling = name_to_string(name)
    candidate_details = rank_candidates(Keyword.get(opts, :candidates, []), spelling, namespace, opts)
    candidates = Enum.map(candidate_details, & &1.name)
    available_candidates = Keyword.get(opts, :available_candidates, [])
    available_names = available_candidates |> Enum.map(&suggestion_name/1) |> Enum.uniq()

    body =
      case available_names do
        [] ->
          Doc.paragraph(
            "`#{Keyword.get(opts, :display_name, spelling)}` is not available in this #{namespace} namespace."
          )

        names ->
          Doc.stack([
            Doc.paragraph(
              "`#{Keyword.get(opts, :display_name, spelling)}` is not available in this #{namespace} namespace."
            ),
            Doc.paragraph("The matched type provides #{Enum.map_join(names, ", ", &"`#{&1}`")}.")
          ])
      end

    suggestions =
      case {candidate_suggestions(candidate_details, spelling, opts), available_names} do
        {[], [_ | _] = names} ->
          [
            %Suggestion{
              message: "Use one of the matched type's constructors: #{Enum.map_join(names, ", ", &"`#{&1}`")}",
              applicability: :manual
            }
          ]

        {ranked, _names} ->
          ranked
      end

    Diagnostic.new(
      code: "E091",
      key: :unknown_name,
      severity: :error,
      title: "Unknown #{namespace_title(namespace)}",
      body: body,
      primary: primary(opts, "`#{spelling}` was not found"),
      notes: Keyword.get(opts, :notes, []),
      suggestions: suggestions,
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        namespace: namespace,
        name: spelling,
        candidates: candidates,
        candidate_details: candidate_details,
        available_candidates: available_candidates,
        owner: Keyword.get(opts, :owner),
        record: Keyword.get(opts, :record),
        checking: Keyword.get(opts, :checking),
        arity: Keyword.get(opts, :arity),
        expected_namespace: Keyword.get(opts, :expected_namespace),
        imported_from: Keyword.get(opts, :imported_from),
        kernel_context: Keyword.get(opts, :kernel_context)
      }
    )
  end

  @doc false
  def rank_candidates(candidates, spelling, namespace, opts \\ []),
    do: Suggest.rank(candidates, spelling, namespace, opts)

  @doc false
  def candidate_suggestions([], _spelling, _opts), do: []

  def candidate_suggestions(candidates, spelling, opts) do
    names = Enum.map(candidates, &suggestion_name/1)

    qualification_hint =
      if Enum.any?(candidates, &requires_qualification?/1), do: " Qualify it or import its module.", else: ""

    {applicability, edits} = unique_name_repair(candidates, spelling, opts)

    [
      %Suggestion{
        message: "Did you mean #{Enum.map_join(names, ", ", &"`#{&1}`")}?#{qualification_hint}",
        applicability: applicability,
        edits: edits
      }
    ]
  end

  defp unique_name_repair(
         [%{name: replacement, imported: imported, requires_import: requires_import}],
         spelling,
         opts
       ) do
    case Keyword.get(opts, :span) do
      %Span{} = span when imported != false and requires_import != true and replacement != spelling ->
        {:machine_applicable, [%TextEdit{span: span, replacement: replacement}]}

      _ ->
        {:maybe_incorrect, []}
    end
  end

  defp unique_name_repair(_candidates, _spelling, _opts), do: {:maybe_incorrect, []}

  defp requires_qualification?(%{imported: false}), do: true
  defp requires_qualification?(%{requires_import: true}), do: true
  defp requires_qualification?(_candidate), do: false

  defp suggestion_name(%{name: name, owner: owner, imported: false}) when not is_nil(owner),
    do: "#{name_to_string(owner)}.#{name}"

  defp suggestion_name(%{name: name}), do: name
  defp suggestion_name(name), do: name_to_string(name)

  defp primary(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span ->
        %Label{span: span, style: :primary, message: Keyword.get(opts, :label, default_message)}

      nil ->
        nil
    end
  end

  defp namespace_title(:value), do: "value"
  defp namespace_title(:constructor), do: "constructor"
  defp namespace_title(:type), do: "type"
  defp namespace_title(:module), do: "module"
  defp namespace_title(:member), do: "module member"
  defp namespace_title(:interface), do: "interface"
  defp namespace_title(other), do: to_string(other)

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
