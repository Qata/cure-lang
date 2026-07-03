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

  @doc """
  Seed an env with the canonical `Bool` (`False | True`) and `Nat` (`Z | S(Nat)`)
  families, each validated against its schema and registered under its builtin
  key. This is the base env for kernel unit tests and the conformance harness
  (the prelude compile obtains the same families via its `@builtin` declarations;
  Task 4 pins the two representations equal).
  """
  @spec seed(Env.t()) :: Env.t()
  def seed(%Env{} = env) do
    env
    |> declare_and_register(:bool, bool_family(), bool_ctors())
    |> declare_and_register(:nat, nat_family(), nat_ctors())
  end

  defp declare_and_register(env, key, family, ctors) do
    fid = family.name
    env = Inductive.declare(env, family, ctors)
    :ok = validate!(env, key, fid)
    Inductive.register_builtin(env, key, fid)
  end

  # Bool : Type0 = False | True  (both nullary)
  defp bool_family, do: Inductive.family(:Bool, [], [], 0)

  defp bool_ctors,
    do: [
      Inductive.ctor(:False, [], []),
      Inductive.ctor(:True, [], [])
    ]

  # Nat : Type0 = Z | S(Nat)  (S's field references the Nat family)
  defp nat_family, do: Inductive.family(:Nat, [], [], 0)

  defp nat_ctors,
    do: [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, {:data, :Nat, [], []}}], [])
    ]
end
