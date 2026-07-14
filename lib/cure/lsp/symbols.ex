defmodule Cure.LSP.Symbols do
  @moduledoc """
  Symbol extraction from Cure AST for LSP features.

  Builds a list of symbols (modules, functions, types, and lifted behavior
  modules) from a parsed
  AST, suitable for `textDocument/documentSymbol` responses.
  """

  @doc """
  Extract symbols from a parsed AST.

  Returns a list of LSP DocumentSymbol maps.
  """
  @spec extract(tuple()) :: [map()]
  def extract(ast) do
    case ast do
      {:container, meta, body} -> extract_generic_container(meta, body)
      {:lift_module, meta, _body} -> extract_lift_module(meta)
      {:block, _, children} -> Enum.flat_map(children, &extract/1)
      _ -> []
    end
  end

  defp extract_lift_module(meta) when is_list(meta) do
    name = Keyword.get(meta, :module, "unnamed")
    behavior = Keyword.get(meta, :behaviour, :unknown)
    line = Keyword.get(meta, :line, 1)
    declarations = Keyword.get(meta, :declarations, [])
    callbacks = Keyword.get(meta, :callbacks, [])

    callback_symbols =
      Enum.map(callbacks, fn callback ->
        callback_symbol(callback, line)
      end)

    [
      %{
        "name" => to_string(name),
        "kind" => 2,
        "range" => lsp_range(line),
        "selectionRange" => lsp_range(line),
        "detail" => "lifted #{behavior} module",
        "children" => callback_symbols ++ Enum.flat_map(declarations, &extract_body_item/1)
      }
    ]
  end

  defp callback_symbol(%{name: name, arity: arity, line: line}, _default_line) do
    %{
      "name" => "callback #{name}/#{arity}",
      "kind" => 12,
      "detail" => "callback #{name}/#{arity}",
      "range" => lsp_range(line),
      "selectionRange" => lsp_range(line)
    }
  end

  defp callback_symbol(%{name: name}, default_line),
    do: callback_symbol(%{name: name, arity: 0, line: default_line}, default_line)

  defp extract_generic_container(meta, body) do
    type = Keyword.get(meta, :container_type, :unknown)
    name = Keyword.get(meta, :name, "unnamed")
    line = Keyword.get(meta, :line, 1)

    kind =
      case type do
        :module -> 2
        :protocol -> 11
        :trait -> 12
        :struct -> 23
        _ -> 2
      end

    children = Enum.flat_map(body, &extract_body_item/1)

    [
      %{
        "name" => name,
        "kind" => kind,
        "range" => lsp_range(line),
        "selectionRange" => lsp_range(line),
        "detail" => to_string(type),
        "children" => children
      }
    ]
  end

  defp extract_body_item({:function_def, meta, _body}) do
    name = Keyword.get(meta, :name, "unknown")
    arity = Keyword.get(meta, :arity, 0)
    line = Keyword.get(meta, :line, 1)
    visibility = Keyword.get(meta, :visibility, :public)

    detail =
      if visibility == :private, do: "local fn #{name}/#{arity}", else: "fn #{name}/#{arity}"

    [
      %{
        "name" => "#{name}/#{arity}",
        "kind" => 12,
        "detail" => detail,
        "range" => lsp_range(line),
        "selectionRange" => lsp_range(line)
      }
    ]
  end

  defp extract_body_item({:container, meta, body}) do
    extract_generic_container(meta, body)
  end

  defp extract_body_item({:type_annotation, meta, _children}) do
    name = Keyword.get(meta, :name, "unknown")
    line = Keyword.get(meta, :line, 1)

    [
      %{
        "name" => name,
        "kind" => 26,
        "range" => lsp_range(line),
        "selectionRange" => lsp_range(line)
      }
    ]
  end

  defp extract_body_item(_), do: []

  defp lsp_range(line) do
    l = max(line - 1, 0)
    %{"start" => %{"line" => l, "character" => 0}, "end" => %{"line" => l, "character" => 999}}
  end
end
