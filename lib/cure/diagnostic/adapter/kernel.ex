defmodule Cure.Diagnostic.Adapter.Kernel do
  @moduledoc "Converts trusted-kernel rejection values into authored diagnostics."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:non_strictly_positive, constructor}, opts),
    do: positivity_failure(constructor, %{}, opts)

  def from_error({:source_context, {:non_strictly_positive, constructor}, context}, opts)
      when is_map(context) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    positivity_failure(constructor, context, opts)
  end

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp positivity_failure(constructor, context, opts) do
    family = Map.get(context, :family_name)
    precise? = Map.get(context, :precise_occurrence, false)
    constructor_name = surface_name(constructor)

    {title, body, primary_message, hint} =
      if precise? and is_binary(family) do
        {
          "Recursive type appears in a function input",
          "`#{family}` appears in a function input stored by `#{constructor_name}`. A recursive type may appear in a stored function's result, but not in one of its inputs.",
          "recursive `#{family}` is consumed here",
          "Move `#{family}` to the function result, or make the input non-recursive"
        }
      else
        {
          "Non-strictly-positive type",
          "The recursive occurrence in `#{constructor_name}` cannot be proven strictly positive, so this type cannot be accepted by the normalising kernel.",
          "this constructor is not strictly positive",
          "Move recursive types out of function-input and other negative positions in this constructor"
        }
      end

    secondary =
      if precise? do
        case label(Map.get(context, :constructor_span), :secondary, "this constructor stores the unsafe function type") do
          nil -> []
          label -> [label]
        end
      else
        []
      end

    Diagnostic.new(
      code: "E103",
      key: :non_strictly_positive_type,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{family: family, constructor: constructor, precise_occurrence: precise?}
    )
  end

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      _ -> nil
    end
  end

  defp label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp label(_, _style, _message), do: nil

  defp surface_name(name) do
    name
    |> name_to_string()
    |> String.split("#")
    |> List.last()
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
