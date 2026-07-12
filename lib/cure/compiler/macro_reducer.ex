defmodule Cure.Compiler.MacroReducer do
  @moduledoc """
  Pure reducer-style AST construction on top of advisory macro reflection.

  The builder only uses constructor signatures to shape patterns. The returned
  AST is ordinary untrusted surface syntax and must still be elaborated by the
  dependent pipeline before it can run.
  """

  alias Cure.Compiler.MacroReflection
  alias Cure.Core.Env

  @type arm_spec :: %{
          required(:constructor) => atom(),
          optional(:bindings) => [String.t()],
          required(:body) => term()
        }

  @spec build_match(String.t() | atom(), term(), [arm_spec()], Env.t()) ::
          {:ok, term()} | {:error, term()}
  def build_match(type_name, scrutinee, arm_specs, %Env{} = env) when is_list(arm_specs) do
    with {:ok, constructors} <- MacroReflection.constructors(env, type_name),
         :ok <- validate_arm_set(constructors, arm_specs),
         {:ok, arms} <- build_arms(constructors, arm_specs) do
      {:ok, {:pattern_match, [generated_by: :macro_reducer], [scrutinee | arms]}}
    end
  end

  defp validate_arm_set(constructors, arm_specs) do
    expected = constructors |> Enum.map(& &1.name) |> MapSet.new()
    actual = arm_specs |> Enum.map(& &1.constructor) |> MapSet.new()

    cond do
      MapSet.size(actual) != length(arm_specs) ->
        {:error, :duplicate_reducer_constructor}

      not MapSet.subset?(actual, expected) ->
        {:error, {:unknown_reducer_constructor, MapSet.difference(actual, expected) |> MapSet.to_list()}}

      actual != expected ->
        {:error, {:incomplete_reducer, MapSet.difference(expected, actual) |> MapSet.to_list()}}

      true ->
        :ok
    end
  end

  defp build_arms(constructors, arm_specs) do
    by_name = Map.new(arm_specs, &{&1.constructor, &1})

    Enum.reduce_while(constructors, {:ok, []}, fn ctor, {:ok, acc} ->
      spec = Map.fetch!(by_name, ctor.name)
      bindings = Map.get(spec, :bindings, [])

      if length(bindings) != length(ctor.args) do
        {:halt, {:error, {:reducer_arity, ctor.name, length(bindings), length(ctor.args)}}}
      else
        pattern = {:function_call, [name: Atom.to_string(ctor.name)], Enum.map(bindings, &variable/1)}
        {:cont, {:ok, acc ++ [{:match_arm, [pattern: pattern], [spec.body]}]}}
      end
    end)
  end

  defp variable(name), do: {:variable, [scope: :local], name}
end
