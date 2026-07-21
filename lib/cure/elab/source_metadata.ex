defmodule Cure.Elab.SourceMetadata do
  @moduledoc """
  Ephemeral authored-source metadata for the active elaboration process.

  These ranges support related diagnostic labels but deliberately never enter
  `Cure.Core.Env`, Core terms, caches, hashes, or serialized artifacts.
  """

  @parameter_key {__MODULE__, :parameter_spans}
  @equation_key {__MODULE__, :equations}

  def put_parameter_spans(name, spans) when is_atom(name) and is_list(spans) do
    Process.put(@parameter_key, Map.put(Process.get(@parameter_key, %{}), name, spans))
    :ok
  end

  def parameter_spans(name) when is_atom(name), do: Process.get(@parameter_key, %{}) |> Map.get(name, [])

  def put_equation(theorem, metadata) when is_atom(theorem) and is_map(metadata) do
    Process.put(@equation_key, Map.put(Process.get(@equation_key, %{}), theorem, metadata))
    :ok
  end

  def equation(theorem) when is_atom(theorem), do: Process.get(@equation_key, %{}) |> Map.get(theorem, %{})
end
