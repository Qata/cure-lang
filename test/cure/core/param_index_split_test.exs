defmodule Cure.Core.ParamIndexSplitTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @type0 {:type, 0}
  @dec {:data, :Dec, [], []}

  # P(a: Type) indices (n: Dec) with wrap : (p: a) -> P(a, Causal).
  # In the ctor telescope check_ctor binds params first (a), then args (p):
  #   ctx_full = [a, p]  → a is {:var, 1} (num_args=1 + (num_params-1-0)=0).
  # result_params = [a] = [{:var, 1}]; result_indices = [Causal].
  defp param_env do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Dec, [], [], 0),
      [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
    )
    |> Inductive.declare(
      Inductive.family(:P, [{:a, @type0}], [{:n, @dec}], 1),
      [
        Inductive.ctor(:wrap, [{:p, {:var, 0}}], [{:ctor, :Causal, []}],
          [:present], [{:var, 1}])
      ]
    )
  end

  test "family carries a non-empty parameter telescope and param_count" do
    env = param_env()
    assert Inductive.param_telescope(env, :P) == [{:a, @type0}]
    assert Inductive.index_telescope(env, :P) == [{:n, @dec}]
    assert Inductive.param_count(env, :P) == 1
    assert Inductive.param_count(env, :Dec) == 0
  end

  test "constructor records result_params and result_indices separately" do
    env = param_env()
    assert Inductive.ctor_result_params(env, :wrap) == [{:var, 1}]
    assert Inductive.ctor_result_indices(env, :wrap) == [{:ctor, :Causal, []}]
  end

  test "3- and 4-arity ctor builders default result_params to []" do
    c3 = Inductive.ctor(:mk, [], [])
    c4 = Inductive.ctor(:mk, [], [], [])
    assert c3.result_params == []
    assert c4.result_params == []
  end
end
