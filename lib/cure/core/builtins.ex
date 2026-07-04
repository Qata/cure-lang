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
    nat: [{:Z, 0}, {:S, 1}],
    eq: [{:refl, 1}]
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
  @spec seed(Env.t(), MapSet.t()) :: Env.t()
  def seed(%Env{} = env, exclude \\ MapSet.new()) do
    env
    |> maybe_seed(:bool, bool_family(), bool_ctors(), exclude)
    |> maybe_seed(:nat, nat_family(), nat_ctors(), exclude)
    |> maybe_seed(:eq, eq_family(), eq_ctors(), exclude)
  end

  # A builtin whose bare family name is locally declared by the compiled module
  # is NOT seeded: the module's own declaration is the canonical family, and
  # pre-seeding a same-named family would leave the seed's constructors in
  # `ctor_to_family` (so a `match` on the local family reads as non-exhaustive).
  defp maybe_seed(env, key, family, ctors, exclude) do
    if MapSet.member?(exclude, family.name) do
      env
    else
      declare_and_register(env, key, family, ctors)
    end
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

  # Eq : (a : Type) -> a -> a -> Type   (1 parameter `a`, 2 indices `x y : a`)
  #   refl : {w : a} -> Eq(a, w, w)     (single ctor, witness `w` erased/forced)
  #
  # The genuine inductive identity type (spec 2026-07-04), retiring the primitive
  # `{:eq}`/`{:refl}`/`{:rewrite}` Core forms. This is the byte-for-byte mirror of
  # the user-level `type MyEq(a) indices (x,y)  mrefl : MyEq(a,w,w)` (oracle
  # `dotpat/dp01`): the de Bruijn shapes below are exactly what that GADT lowers
  # to, with names MyEq→Eq / mrefl→refl. `w` is erased (quantity 0) so it is
  # forced by index unification when matching `refl` and dropped at runtime, while
  # the surface still supplies it explicitly at construction (`refl(x)`). K/UIP is
  # inherited from the existing index unifier — operator-signed-off 2026-07-04.
  defp eq_family,
    do: Inductive.family(:Eq, [a: {:type, 0}], [x: {:var, 0}, y: {:var, 1}], 0)

  defp eq_ctors,
    do: [
      Inductive.ctor(:refl, [w: {:var, 0}], [{:var, 0}, {:var, 0}], [:erased], [{:var, 1}])
    ]
end
