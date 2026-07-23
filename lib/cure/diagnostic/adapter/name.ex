defmodule Cure.Diagnostic.Adapter.Name do
  @moduledoc """
  Converts unresolved-name failures and owns deterministic candidate repairs.

  Candidate maps retain semantic identity, owner, namespace, visibility,
  qualification/import requirements, arity, and origin in the machine payload.
  """

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion, TextEdit}
  alias Cure.Diagnostic.Suggest

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:unknown_global, name}, opts), do: unknown_name(:value, name, opts)
  def from_error({:unbound_var, name}, opts), do: unknown_name(:value, name, opts)
  def from_error({:unknown_family, name}, opts), do: unknown_name(:type, name, opts)
  def from_error({:unknown_ctor, name}, opts), do: unknown_name(:constructor, name, opts)
  def from_error({:foreign_ctor, name}, opts), do: unknown_name(:constructor, name, opts)
  def from_error({:unknown_constructor, name}, opts), do: unknown_name(:constructor, name, opts)

  def from_error({:unknown_global, name, details}, opts) when is_map(details),
    do: unknown_name(:value, name, Keyword.put(opts, :kernel_context, details))

  def from_error({:unknown_name, details}, opts) when is_map(details) do
    namespace = Map.get(details, :namespace, :value)
    name = Map.get(details, :name, "<unknown>")

    unknown_name(
      namespace,
      name,
      opts
      |> Keyword.put(:candidates, Map.get(details, :candidates, []))
      |> Keyword.put(:owner, Map.get(details, :owner))
      |> Keyword.put(:checking, Map.get(details, :checking))
      |> Keyword.put(:arity, Map.get(details, :arity))
      |> Keyword.put(:expected_namespace, Map.get(details, :expected_namespace))
      |> Keyword.put(:imported_from, Map.get(details, :imported_from))
      |> Keyword.put(:span, Map.get(details, :span))
      |> Keyword.put(:provenance, Map.get(details, :provenance, []))
    )
  end

  def from_error({:unknown_field, record, field}, opts) do
    unknown_name(:member, "#{name_to_string(record)}.#{name_to_string(field)}", Keyword.put(opts, :owner, record))
  end

  def from_error({:source_context, {:unknown_field, record, field}, context}, opts) when is_map(context) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(context, :span))
      |> Keyword.put(:owner, record)
      |> Keyword.put(:checking, Map.get(context, :checking))

    unknown_name(:member, "#{name_to_string(record)}.#{name_to_string(field)}", opts)
  end

  def from_error({:source_context, {:unknown_field, record, field, available_fields}, context}, opts)
      when is_map(context) and is_list(available_fields),
      do: record_field_unknown(record, field, available_fields, context, opts)

  def from_error({:unknown_field, record, field, available_fields}, opts) when is_list(available_fields) do
    candidates =
      Enum.map(available_fields, fn candidate ->
        %{
          id: {:record_field, record, candidate},
          name: name_to_string(candidate),
          namespace: :member,
          owner: record,
          imported: true,
          origin: :record_shape
        }
      end)

    opts =
      opts
      |> Keyword.put(:owner, record)
      |> Keyword.put(:record, record)
      |> Keyword.put(:candidates, candidates)
      |> Keyword.put(:display_name, "#{name_to_string(record)}.#{name_to_string(field)}")

    unknown_name(:member, name_to_string(field), opts)
  end

  def from_error({:source_context, {kind, name}, context}, opts)
      when kind in [:unknown_ctor, :unknown_pattern_constructor, :unknown_family] and
             is_map(context) do
    opts =
      opts
      |> Keyword.put_new(:span, Map.get(context, :span))
      |> Keyword.put(:candidates, Map.get(context, :name_candidates, []))
      |> Keyword.put(:available_candidates, Map.get(context, :name_candidates, []))
      |> Keyword.put(:arity, Map.get(context, :name_arity))
      |> Keyword.put(:checking, Map.get(context, :checking))

    namespace = if kind == :unknown_family, do: :type, else: :constructor
    unknown_name(namespace, name, opts)
  end

  def from_error({:source_context, {:foreign_ctor, constructor}, context}, opts) when is_map(context),
    do: foreign_constructor(constructor, context, opts)

  def from_error({:no_such_interface, %{interface: interface} = details}, opts) do
    opts =
      opts
      |> Keyword.put(:span, Map.get(details, :span) || Keyword.get(opts, :span))
      |> Keyword.put(:candidates, Map.get(details, :candidates, []))

    unknown_name(:interface, interface, opts)
  end

  def from_error({:no_such_interface, interface}, opts),
    do: unknown_name(:interface, interface, opts)

  def from_error({:unknown_interface_method, interface, method}, opts),
    do: unknown_name(:member, method, Keyword.put(opts, :checking, interface))

  def from_error({:unknown_interface_method, %{interface: interface, method: method} = details}, opts) do
    opts =
      opts
      |> Keyword.put(:span, Map.get(details, :span) || Keyword.get(opts, :span))
      |> Keyword.put(:checking, interface)
      |> Keyword.put(:candidates, Map.get(details, :candidates, []))

    unknown_name(:member, method, opts)
  end

  def from_error({:ambiguous_name, name, modules}, opts) when is_list(modules),
    do: ambiguous_name(name, modules, opts)

  def from_error({:ambiguous_method, method, interfaces}, opts) when is_list(interfaces),
    do: ambiguous_member(method, interfaces, opts)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  @doc false
  def ambiguous_name(name, modules, opts \\ []) do
    spelling = name_to_string(name)
    owners = Enum.map(modules, &name_to_string/1)

    Diagnostic.new(
      code: "E089",
      key: :ambiguous_name,
      severity: :error,
      title: "Ambiguous name",
      body: Doc.paragraph("`#{spelling}` is provided by more than one imported module."),
      primary: primary(opts, "qualification is required here"),
      suggestions: [
        %Suggestion{
          message: "Qualify the name as #{Enum.map_join(owners, " or ", &"`#{&1}.#{spelling}`")}",
          applicability: :manual
        }
      ],
      payload: %{namespace: :value, name: spelling, owners: owners}
    )
  end

  @doc false
  def ambiguous_member(method, interfaces, opts \\ []),
    do: ambiguous_member(method, interfaces, %{}, opts)

  def ambiguous_member(method, interfaces, context, opts) do
    spelling = name_to_string(method)
    owners = Enum.map(interfaces, &name_to_string/1)
    primary_span = Map.get(context, :span) || Keyword.get(opts, :span)

    declarations =
      context
      |> Map.get(:method_declarations, [])
      |> Enum.filter(&match?(%{span: %Span{}}, &1))

    secondary =
      declarations
      |> Enum.reject(&(&1.span == primary_span))
      |> Enum.map(fn declaration ->
        %Label{
          span: declaration.span,
          style: :secondary,
          message: "`#{spelling}` is also declared by `#{name_to_string(declaration.interface)}` here"
        }
      end)

    primary_owner =
      Enum.find_value(declarations, fn declaration ->
        if declaration.span == primary_span, do: name_to_string(declaration.interface)
      end)

    owner_list = Enum.map_join(owners, " and ", &"`#{&1}`")

    Diagnostic.new(
      code: "E089",
      key: :ambiguous_name,
      severity: :error,
      title: "Method `#{spelling}` is declared by multiple interfaces",
      body:
        Doc.paragraph(
          "Both #{owner_list} declare `#{spelling}`. Interface methods share one unqualified namespace, so Cure could not determine which declaration an unqualified `#{spelling}(...)` call should use."
        ),
      primary:
        if(primary_span,
          do: %Label{
            span: primary_span,
            style: :primary,
            message:
              if(primary_owner,
                do: "`#{primary_owner}` repeats the interface method `#{spelling}`",
                else: "this repeats the interface method `#{spelling}`"
              )
          },
          else: primary(opts, "rename this interface method")
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Rename `#{spelling}` in one interface so every interface method has a unique name",
          applicability: :manual
        }
      ],
      payload: %{
        kind: :ambiguous_method,
        method: spelling,
        interfaces: owners,
        declarations:
          Enum.map(declarations, fn declaration ->
            %{interface: name_to_string(declaration.interface)}
          end)
      }
    )
  end

  @doc false
  def record_field_unknown(record, field, available_fields, context, opts) do
    record_name = surface_name(record)
    field = name_to_string(field)
    field_span = Map.get(context, :field_span) || Map.get(context, :span)
    receiver_span = Map.get(context, :receiver_span)

    candidates =
      Enum.map(available_fields, fn candidate ->
        %{
          id: {:record_field, record, candidate},
          name: name_to_string(candidate),
          namespace: :member,
          owner: record,
          imported: true,
          origin: :record_shape
        }
      end)

    ranking_opts =
      opts
      |> Keyword.put(:span, field_span)
      |> Keyword.put(:owner, record)
      |> Keyword.put(:record, record)

    candidate_details = rank_candidates(candidates, field, :member, ranking_opts)

    secondary =
      case receiver_span do
        %Span{} = span when span != field_span ->
          [%Label{span: span, style: :secondary, message: "this value has record type `#{record_name}`"}]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E091",
      key: :unknown_name,
      severity: :error,
      title: "`#{record_name}` has no field `#{field}`",
      body: Doc.paragraph("The record `#{record_name}` does not declare a field named `#{field}`."),
      primary:
        if(field_span,
          do: %Label{span: field_span, style: :primary, message: "`#{record_name}` has no field named `#{field}`"}
        ),
      secondary: secondary,
      suggestions: candidate_suggestions(candidate_details, field, ranking_opts),
      payload: %{
        namespace: :member,
        name: field,
        owner: record,
        record: record,
        candidates: Enum.map(candidate_details, & &1.name),
        candidate_details: candidate_details,
        checking: Map.get(context, :checking)
      }
    )
  end

  @doc false
  def foreign_constructor(constructor, context, opts) do
    constructor_id = name_to_string(constructor)
    constructor_name = surface_name(constructor)
    actual_family_id = Map.get(context, :actual_family)
    expected_family_id = Map.get(context, :expected_family)
    actual_family = surface_name(actual_family_id)
    expected_family = surface_name(expected_family_id)

    pattern_span =
      context
      |> Map.get(:branch_patterns, [])
      |> Enum.find_value(fn pattern ->
        if name_to_string(Map.get(pattern, :name)) == constructor_name,
          do: Map.get(pattern, :pattern_span) || Map.get(pattern, :span)
      end)

    primary_span = pattern_span || Map.get(context, :span) || Keyword.get(opts, :span)

    secondary =
      case Map.get(context, :expectation_span) do
        %Span{} = span when span != primary_span ->
          [%Label{span: span, style: :secondary, message: "this match expects constructors from `#{expected_family}`"}]

        _ ->
          []
      end

    expected_constructor_ids = Map.get(context, :expected_constructors, [])
    expected_constructors = Enum.map(expected_constructor_ids, &surface_name/1)

    suggestions =
      case {expected_constructors, primary_span} do
        {[replacement], %Span{} = span} ->
          [
            %Suggestion{
              message: "Replace `#{constructor_name}` with `#{replacement}`",
              applicability: :machine_applicable,
              edits: [%TextEdit{span: span, replacement: replacement <> "()"}]
            }
          ]

        {[_ | _] = constructors, _span} ->
          [
            %Suggestion{
              message: "Use one of #{Enum.map_join(constructors, ", ", &"`#{&1}`")}",
              applicability: :manual
            }
          ]

        _ ->
          []
      end

    Diagnostic.new(
      code: "E091",
      key: :unknown_name,
      severity: :error,
      title: "`#{constructor_name}` does not belong to `#{expected_family}`",
      body:
        Doc.paragraph(
          "`#{constructor_name}` is a constructor of `#{actual_family}`, but this match scrutinizes `#{expected_family}`. Every constructor pattern must come from the scrutinee's type."
        ),
      primary:
        if(primary_span,
          do: %Label{
            span: primary_span,
            style: :primary,
            message: "this constructor belongs to `#{actual_family}`, not `#{expected_family}`"
          },
          else: primary(opts, "use a constructor from the matched type")
        ),
      secondary: secondary,
      suggestions: suggestions,
      payload: %{
        kind: :foreign_ctor,
        constructor: constructor_name,
        constructor_id: constructor_id,
        actual_family: actual_family,
        actual_family_id: name_to_string(actual_family_id),
        expected_family: expected_family,
        expected_family_id: name_to_string(expected_family_id),
        expected_constructors: expected_constructors,
        expected_constructor_ids: Enum.map(expected_constructor_ids, &name_to_string/1)
      }
    )
  end

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

  defp surface_name(name) do
    name
    |> name_to_string()
    |> String.split("#")
    |> List.last()
  end
end
