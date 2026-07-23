defmodule Cure.Diagnostic.Adapter.StaticAnalysis do
  @moduledoc "Converts whole-definition static-analysis rejections with authored source context."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:erased_used_relevantly, details}, opts) when is_map(details),
    do: relevance_failure(details, %{}, opts)

  def from_error({:source_context, {:erased_used_relevantly, details}, context}, opts)
      when is_map(details) and is_map(context) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    relevance_failure(details, context, opts)
  end

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp relevance_failure(details, context, opts) do
    site = Map.get(details, :site, :runtime)
    binder = Map.get(details, :binder)
    binder_name = Map.get(context, :binder_name)

    subject =
      cond do
        is_binary(binder_name) -> "The erased parameter `#{binder_name}`"
        is_atom(binder_name) and not is_nil(binder_name) -> "The erased parameter `#{binder_name}`"
        is_nil(binder) -> "An erased value"
        true -> "Erased binder #{binder}"
      end

    secondary =
      case label(
             Map.get(context, :binder_span),
             :secondary,
             "`#{binder_name || "this value"}` is erased here"
           ) do
        nil -> []
        label -> [label]
      end

    Diagnostic.new(
      code: "E104",
      key: :erased_value_used_relevantly,
      severity: :error,
      title: "Erased value used relevantly",
      body:
        Doc.paragraph("#{subject} is used as #{site_description(site)}, but erased parameters do not exist at runtime."),
      primary: primary(opts, primary_message(site)),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: suggestion(binder_name),
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  defp primary_message(:returned), do: "this returns an erased value at runtime"
  defp primary_message(:present_arg), do: "this passes an erased value to a runtime argument"
  defp primary_message(:scrutinee), do: "this match inspects an erased value at runtime"
  defp primary_message(:applied), do: "this applies an erased value as a runtime function"
  defp primary_message(_site), do: "this uses an erased value at runtime"

  defp site_description(:returned), do: "the function's runtime result"
  defp site_description(:present_arg), do: "an argument that exists at runtime"
  defp site_description(:scrutinee), do: "the value inspected by a runtime match"
  defp site_description(:applied), do: "a function called at runtime"
  defp site_description(_site), do: "a value needed at runtime"

  defp suggestion(name) when is_binary(name) or (is_atom(name) and not is_nil(name)),
    do: "Declare `#{name}` as a runtime parameter, or keep it out of runtime expressions"

  defp suggestion(_name),
    do: "Use a runtime parameter here, or keep the erased value out of runtime expressions"

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      _ -> nil
    end
  end

  defp label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp label(_, _style, _message), do: nil
end
