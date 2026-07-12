defmodule Cure.Compiler.MacroCheck do
  @moduledoc "Pure property-plan builder for macro library self-checks."

  @property_kinds [:round_trip, :total, :fault_rejection, :exhaustive, :termination]

  @spec plan(String.t() | atom(), [map()]) :: {:ok, map()} | {:error, term()}
  def plan(name, properties) when is_list(properties) do
    names = Enum.map(properties, &Map.get(&1, :name))

    cond do
      Enum.any?(properties, fn property -> not valid_property?(property) end) ->
        {:error, :invalid_check_property}

      length(names) != MapSet.size(MapSet.new(names)) ->
        {:error, :duplicate_check_property}

      true ->
        {:ok,
         %{
           kind: :quoted_check_plan,
           name: name,
           properties: properties,
           declarations: [{:check_def, [name: name], properties}]
         }}
    end
  end

  defp valid_property?(%{name: name, kind: kind, expression: _expression})
       when (is_atom(name) or is_binary(name)) and kind in @property_kinds,
       do: true

  defp valid_property?(_), do: false
end
