defmodule Cure.Elab.HoleIdentityTest do
  @moduledoc """
  Every source `?` must lower to a UNIQUE, deterministic hole id (first-class
  holes, Slice 1). This is the soundness pivot: once holes are stuck neutrals
  that flow through conversion, two holes sharing an id are definitionally equal,
  so `refl : ?a = ?b` would type-check. Distinct ids per occurrence prevent that.
  Determinism (positional/name-derived, no gensym counter) keeps Antigen and the
  differential oracle replay-stable.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @src """
  mod Holes
    fn a() -> Type = ?
    fn b() -> Type = ?
    fn c() -> Type = ?goal
  end
  """

  defp hole_ids(env) do
    env.defs
    |> Map.values()
    |> Enum.map(& &1.body)
    |> Enum.filter(&match?({:hole, _}, &1))
    |> Enum.map(fn {:hole, id} -> id end)
  end

  test "each source ? lowers to a unique, non-empty hole id" do
    {:ok, env} = Program.elaborate(@src)
    ids = hole_ids(env)

    assert length(ids) == 3
    assert Enum.all?(ids, &(is_binary(&1) and &1 != "")),
           "every hole id must be a non-empty string: #{inspect(ids)}"

    assert length(Enum.uniq(ids)) == 3,
           "hole ids must be distinct per source occurrence: #{inspect(ids)}"
  end

  test "a named hole ?goal carries its name in the id" do
    {:ok, env} = Program.elaborate(@src)
    ids = hole_ids(env)
    assert Enum.any?(ids, &String.contains?(&1, "goal")), "?goal must keep its name: #{inspect(ids)}"
  end

  test "elaboration is deterministic — identical source yields identical hole ids" do
    {:ok, env1} = Program.elaborate(@src)
    {:ok, env2} = Program.elaborate(@src)
    assert Enum.sort(hole_ids(env1)) == Enum.sort(hole_ids(env2))
  end
end
