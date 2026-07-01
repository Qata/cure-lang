defmodule Cure.Elab.ParamIndexElabTest do
  @moduledoc """
  Task 6/7: the elaborator must read the split `params`/`indices` meta emitted by
  the parser, register a real parameter telescope (not fold everything into
  indices), and split each constructor's applied result vector into
  `result_params` (prefix) ++ `result_indices` (suffix).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive
  alias Cure.Elab.Program

  # A param-bearing indexed family in the new surface syntax. `a` is a uniform
  # parameter restated in the result (`Pair(a, …)`); `tag` is the sole index.
  @src """
  mod M
    type Dec = Dcoupled | Causal
    type Pair(a: Type) indices (tag: Dec)
      mk : a -> a -> Pair(a, Causal)
  """

  test "param-bearing declaration registers split telescopes + result_params" do
    assert {:ok, env} = Program.elaborate(@src)

    assert Inductive.param_count(env, :Pair) == 1
    assert Inductive.param_telescope(env, :Pair) |> length() == 1
    assert Inductive.index_telescope(env, :Pair) |> length() == 1

    # The applied result `Pair(a, Causal)` splits 1 param + 1 index.
    assert Inductive.ctor_result_params(env, :mk) |> length() == 1
    assert Inductive.ctor_result_indices(env, :mk) == [{:ctor, :Causal, []}]

    # And the kernel accepts it: the restated `a` is a uniform parameter.
    fam = Inductive.get_family(env, :Pair)
    ctor = Inductive.get_ctor(env, :mk)
    assert :ok == Cure.Core.Kernel.check_ctor(env, fam, ctor)
  end

  test "a parameter-free indexed family still elaborates (regression)" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type Length indices (n: Nat)
        zero : Length(Z)
    """

    assert {:ok, env} = Program.elaborate(src)
    assert Inductive.param_count(env, :Length) == 0
    assert Inductive.index_telescope(env, :Length) |> length() == 1
    assert Inductive.ctor_result_params(env, :zero) == []
    assert Inductive.ctor_result_indices(env, :zero) |> length() == 1
  end
end
