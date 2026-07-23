defmodule Cure.Diagnostic.Adapter.Declaration do
  @moduledoc "Owns declaration-shape diagnostics for foreign declarations."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Label, Span}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:extern_untyped_head, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E056",
      key: :extern_untyped_head,
      severity: :error,
      title: "@extern declaration missing a typed head",
      message: message,
      primary: primary_label(opts, "add parameter and return type annotations"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  def from_error({:extern_has_body, message, meta}, opts) when is_binary(message) and is_list(meta) do
    Diagnostic.new(
      code: "E057",
      key: :extern_has_body,
      severity: :error,
      title: "@extern declaration has a body",
      message: message,
      primary: primary_label(opts, "remove the body from this extern declaration"),
      payload: %{line: Keyword.get(meta, :line), column: Keyword.get(meta, :col)}
    )
  end

  defp primary_label(opts, default_message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, default_message)}
      nil -> nil
    end
  end
end
