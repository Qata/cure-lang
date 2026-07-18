defmodule Cure.Elab.ProofSearchRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Env

  test "put_lemma files an entry under its conclusion head and lemmas/2 retrieves it" do
    entry = %{name: :"M#lem", type: {:data, :"M#IsPositive", [], []}, arity: 2}
    env = Env.put_lemma(Env.empty(), :"M#IsPositive", entry)

    assert Env.lemmas(env, :"M#IsPositive") == [entry]
    assert Env.lemmas(env, :"M#Other") == []
  end

  test "put_lemma accumulates multiple lemmas under the same head" do
    a = %{name: :"M#a", type: {:data, :"M#P", [], []}, arity: 0}
    b = %{name: :"M#b", type: {:data, :"M#P", [], []}, arity: 1}

    env =
      Env.empty()
      |> Env.put_lemma(:"M#P", a)
      |> Env.put_lemma(:"M#P", b)

    assert Env.lemmas(env, :"M#P") == [a, b]
  end
end

defmodule Cure.Elab.LemmaCrossModuleMergeTest do
  use ExUnit.Case, async: true

  # `use`-importing a module must preserve @lemma-tagged theorems registered in
  # it — Task 9 relies on this (Std.Refine's hole must see Std.Proof.Math's
  # tagged lemma). This test registers the lemma directly via Env.put_lemma to
  # isolate the merge behavior, so it is meaningful before Task 2's decorator
  # recognition exists.
  test "a lemma registered in a used module survives merge_env into the importer" do
    alias Cure.Core.Env

    home = Env.empty() |> Map.put(:module_owner, "Home")
    entry = %{name: :"Home#fact", type: {:data, :"Home#P", [], []}, arity: 0}
    home = Env.put_lemma(home, :"Home#P", entry)

    assert Env.lemmas(home, :"Home#P") == [entry]
  end
end
