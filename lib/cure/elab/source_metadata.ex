defmodule Cure.Elab.SourceMetadata do
  @moduledoc """
  Ephemeral authored-source metadata for the active elaboration process.

  These ranges support related diagnostic labels but deliberately never enter
  `Cure.Core.Env`, Core terms, caches, hashes, or serialized artifacts.
  """

  @key {__MODULE__, :parameter_spans}

  def put_parameter_spans(name, spans) when is_atom(name) and is_list(spans) do
    Process.put(@key, Map.put(Process.get(@key, %{}), name, spans))
    :ok
  end

  def parameter_spans(name) when is_atom(name), do: Process.get(@key, %{}) |> Map.get(name, [])
end
