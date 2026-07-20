defmodule Cure.Diagnostic.SourceRegistry do
  @moduledoc "Immutable source-buffer registry used to resolve diagnostic spans."

  alias Cure.Diagnostic.Span

  defstruct sources: %{}, paths: %{}
  @type t :: %__MODULE__{sources: %{term() => String.t()}, paths: %{term() => String.t() | nil}}

  @spec new() :: t()
  def new, do: %__MODULE__{}

  @spec register(t(), term(), String.t(), String.t() | nil) :: t()
  def register(%__MODULE__{} = registry, source_id, source, path \\ nil) when is_binary(source) do
    %__MODULE__{
      registry
      | sources: Map.put(registry.sources, source_id, source),
        paths: Map.put(registry.paths, source_id, path)
    }
  end

  @spec fetch(t(), term()) :: {:ok, String.t()} | :error
  def fetch(%__MODULE__{sources: sources}, source_id), do: Map.fetch(sources, source_id)

  @spec span(t(), term(), non_neg_integer(), non_neg_integer()) :: {:ok, Span.t()} | {:error, term()}
  def span(%__MODULE__{} = registry, source_id, start_byte, end_byte)
      when is_integer(start_byte) and is_integer(end_byte) and start_byte >= 0 and end_byte >= start_byte do
    with {:ok, source} <- fetch(registry, source_id),
         true <- end_byte <= byte_size(source) do
      {start_line, start_column} = coordinates(source, start_byte)
      {end_line, end_column} = coordinates(source, end_byte)

      {:ok,
       Span.new(
         source_id: source_id,
         path: Map.get(registry.paths, source_id),
         start_byte: start_byte,
         end_byte: end_byte,
         start_line: start_line,
         start_column: start_column,
         end_line: end_line,
         end_column: end_column
       )}
    else
      :error -> {:error, :unknown_source}
      false -> {:error, :span_out_of_bounds}
    end
  end

  @spec line(t(), Span.t(), pos_integer()) :: {:ok, String.t()} | :error
  def line(%__MODULE__{} = registry, %Span{source_id: source_id}, line_number) do
    with {:ok, source} <- fetch(registry, source_id),
         line when is_binary(line) <- Enum.at(String.split(source, "\n"), line_number - 1) do
      {:ok, line}
    else
      _ -> :error
    end
  end

  @doc "Convert a span endpoint to the zero-based UTF-16 position required by LSP."
  @spec lsp_position(t(), Span.t(), :start | :end) :: {:ok, map()} | {:error, term()}
  def lsp_position(%__MODULE__{} = registry, %Span{} = span, endpoint) when endpoint in [:start, :end] do
    byte = if endpoint == :start, do: span.start_byte, else: span.end_byte
    line = if endpoint == :start, do: span.start_line, else: span.end_line

    with {:ok, source} <- fetch(registry, span.source_id),
         true <- byte <= byte_size(source) do
      prefix = binary_part(source, 0, byte)
      line_prefix = prefix |> String.split("\n") |> List.last()
      utf16 = :unicode.characters_to_binary(line_prefix, :utf8, {:utf16, :little})
      {:ok, %{"line" => line - 1, "character" => div(byte_size(utf16), 2)}}
    else
      :error -> {:error, :unknown_source}
      false -> {:error, :span_out_of_bounds}
    end
  end

  # Columns are Unicode scalar columns. LSP's UTF-16 conversion belongs in its adapter.
  defp coordinates(source, byte) do
    prefix = binary_part(source, 0, byte)
    lines = String.split(prefix, "\n")
    {length(lines), String.length(List.last(lines) || "") + 1}
  end
end
