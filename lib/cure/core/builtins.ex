defmodule Cure.Core.Builtins do
  @moduledoc """
  Canonical builtin-inductive schemas and the programmatic seeder.

  Schema validation checks constructor NAMES and arities, not arity alone:
  the literal wiring (true/false -> True/False) and erasure atom mapping
  (False/True -> false/true; Z/S -> int) key off these exact names, so a
  shape-conformant but name-mismatched binding (e.g. `Coin = Heads | Tails`
  tagged `@builtin(:bool)`) is a real miscompile risk and must be rejected.
  """
  alias Cure.Core.{Env, Inductive}

  # key => list of {ctor_name, arity}. Names are load-bearing.
  @schemas %{
    bool: [{:False, 0}, {:True, 0}],
    nat: [{:Z, 0}, {:S, 1}]
  }

  @doc "The expected schema descriptor for a builtin key. Raises for an unknown key."
  @spec schema(atom()) :: [{atom(), non_neg_integer()}]
  def schema(key), do: Map.fetch!(@schemas, key)

  @doc """
  Validate that `family_id` in `env` conforms to `key`'s canonical schema —
  by constructor NAME and arity (not arity alone). `:ok` or raises `ArgumentError`.
  """
  @spec validate!(Env.t(), atom(), atom()) :: :ok
  def validate!(%Env{} = env, key, family_id) do
    expected = Enum.sort(schema(key))
    ctors = Inductive.ctors_of(env, family_id) || []

    actual =
      ctors
      |> Enum.map(fn c -> {c.name, length(Map.get(c, :args, []))} end)
      |> Enum.sort()

    if actual == expected do
      :ok
    else
      raise ArgumentError,
            "@builtin(#{inspect(key)}) on #{inspect(family_id)}: expected constructors " <>
              "#{inspect(expected)} (name and arity), got #{inspect(actual)}"
    end
  end
end
