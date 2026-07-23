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

  def from_error({:usage_violation, details}, opts) when is_map(details),
    do: usage_failure(details, %{}, opts)

  def from_error({:source_context, {:usage_violation, details}, context}, opts)
      when is_map(details) and is_map(context) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    usage_failure(details, context, opts)
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

  defp usage_failure(details, context, opts) do
    declared = Map.get(details, :declared, :unknown)
    used = Map.get(details, :used, :unknown)
    binder = Map.get(details, :binder)
    binder_name = Map.get(context, :binder_name)
    display_name = if binder_name, do: "`#{binder_name}`", else: "A binding"

    {title, body, primary_message, hint} =
      usage_copy(display_name, binder_name, declared, used, Map.get(context, :use_spans, []))

    primary_span = Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E117",
      key: :resource_usage_violation,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, primary_message),
      secondary: usage_secondary_labels(context, primary_span, declared, used),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :binder_name, binder_name || binder)
    )
  end

  defp usage_copy(name, binder_name, :linear, :erased, _uses) do
    action_name = usage_action_name(name, binder_name)

    {
      "Linear value is not used",
      "#{name} is linear, so every path through this function must use it exactly once. This function does not use it.",
      "this linear parameter must be used exactly once",
      "Use #{action_name} once on every path, or declare it `:affine` if it may be dropped"
    }
  end

  defp usage_copy(name, binder_name, :linear, :unrestricted, uses) do
    action_name = usage_action_name(name, binder_name)

    body =
      if length(uses) > 1 do
        "#{name} is linear, but this path can use it more than once. A linear value must be consumed exactly once."
      else
        "#{name} is linear, but this use passes it to a context that may consume it any number of times."
      end

    {
      "Linear value may be used more than once",
      body,
      "this use does not preserve linear ownership",
      "Pass #{action_name} only to linear parameters, and consume it exactly once on every path"
    }
  end

  defp usage_copy(name, binder_name, :affine, :unrestricted, uses) do
    action_name = usage_action_name(name, binder_name)

    body =
      if length(uses) > 1 do
        "#{name} is affine, but this path can use it more than once. An affine value may be used once or not at all."
      else
        "#{name} is affine, but this use passes it to a context that may consume it any number of times."
      end

    {
      "Affine value may be used more than once",
      body,
      "this use does not preserve affine ownership",
      "Pass #{action_name} only to affine or linear parameters, and use it at most once"
    }
  end

  defp usage_copy(name, binder_name, declared, used, _uses) do
    action_name = usage_action_name(name, binder_name)

    {
      "Resource usage violates its grade",
      "#{name} is declared `#{declared}` but its inferred usage is `#{used}`.",
      "this use is incompatible with the declared resource grade",
      "Use #{action_name} according to its declared `#{declared}` grade"
    }
  end

  defp usage_action_name(name, binder_name) when not is_nil(binder_name), do: name
  defp usage_action_name(_name, _binder_name), do: "the binding"

  defp usage_secondary_labels(context, primary_span, declared, :erased) do
    [
      label(
        Map.get(context, :grade_span),
        :secondary,
        "this parameter is declared `#{declared}` here"
      )
    ]
    |> Enum.reject(&is_nil/1)
    |> Enum.reject(&same_span?(&1.span, primary_span))
  end

  defp usage_secondary_labels(context, primary_span, declared, _used) do
    binder =
      label(
        Map.get(context, :binder_span),
        :secondary,
        "this parameter is declared `#{declared}` here"
      )

    earlier_uses =
      context
      |> Map.get(:use_spans, [])
      |> Enum.reject(&same_span?(&1, primary_span))
      |> Enum.map(&label(&1, :secondary, "another use on this path is here"))

    [binder | earlier_uses] |> Enum.reject(&is_nil/1)
  end

  defp same_span?(%Span{} = left, %Span{} = right) do
    left.start_byte == right.start_byte and left.end_byte == right.end_byte and
      left.start_line == right.start_line and left.end_line == right.end_line
  end

  defp same_span?(_left, _right), do: false

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
