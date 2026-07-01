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

  alias Cure.Core.Inductive, as: Ind

  test "check_ctor accepts a uniform parameter constructor" do
    env = param_env()
    fam = Ind.get_family(env, :P)
    ctor = Ind.get_ctor(env, :wrap)
    assert :ok == Kernel.check_ctor(env, fam, ctor)
  end

  test "check_ctor rejects a non-uniform parameter (param slot is not a)" do
    # oddball : P(Bool-ish stand-in, Causal) — param slot is a GROUND family, not
    # the parameter variable a. Use Dcoupled-indexed Dec as a stand-in rigid term.
    env = param_env()
    fam = Ind.get_family(env, :P)
    bad =
      Ind.ctor(:oddball, [], [{:ctor, :Causal, []}], [], [{:data, :Dec, [], []}])
    assert {:error, {:non_uniform_parameter, info}} = Kernel.check_ctor(env, fam, bad)
    assert info.family == :P and info.ctor == :oddball and info.position == 0
  end

  test "check_ctor on a param-free family is unchanged (regression)" do
    env = param_env()
    fam = Ind.get_family(env, :Dec)
    assert :ok == Kernel.check_ctor(env, fam, Ind.get_ctor(env, :Causal))
  end

  test "check_ctor rejects a result_params arity mismatch (wrong count, not just wrong value)" do
    env = param_env()
    fam = Ind.get_family(env, :P)
    # `wrong_arity` supplies zero result_params where the family declares 1 —
    # exercises check_uniform_params' `:arity` branch, which the position-mismatch
    # test above never reaches (it always supplies exactly 1 result_param).
    wrong_arity = Ind.ctor(:wrong_arity, [], [{:ctor, :Causal, []}], [], [])
    assert {:error, {:non_uniform_parameter, info}} = Kernel.check_ctor(env, fam, wrong_arity)
    assert info.family == :P and info.ctor == :wrong_arity and info.position == :arity
  end

  alias Cure.Core.Context

  test "checking a param-bearing constructor application against its expected vdata carries params ++ indices" do
    env = param_env()
    ctx = Context.empty(env)
    a_val = {:vdata, :Dec, []}
    causal_val = {:vctor, :Causal, []}
    term = {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}
    expected = {:vdata, :P, [a_val, causal_val]}
    assert :ok == Kernel.check(ctx, term, expected)
  end

  test "bare inference of a param-bearing constructor application is rejected (no expected type to source params from)" do
    env = param_env()
    ctx = Context.empty(env)
    term = {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}
    assert {:error, {:ctor_requires_checking_mode, :P}} == Kernel.infer(ctx, term)
  end

  test "infer of a param-free constructor is unchanged (regression)" do
    env = param_env()
    ctx = Context.empty(env)
    assert {:ok, {:vdata, :Dec, []}} == Kernel.infer(ctx, {:ctor, :Dcoupled, []})
  end

  test "checking against a mismatched expected vdata is rejected (args checking ok is not enough)" do
    # wrap(d) always produces index Causal — checking it against an expected
    # type whose index is Dcoupled must fail, even though `d` itself checks
    # fine against the parameter slot. Falsifies a clause that only verifies
    # check_ctor_app succeeds without comparing the computed result to `expected`.
    env = param_env()
    ctx = Context.empty(env)
    a_val = {:vdata, :Dec, []}
    causal_val = {:vctor, :Causal, []}
    wrong_index_val = {:vctor, :Dcoupled, []}
    term = {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}
    expected = {:vdata, :P, [a_val, wrong_index_val]}

    assert {:error, {:conversion_failure, {:vdata, :P, [^a_val, ^causal_val]}, ^expected}} =
             Kernel.check(ctx, term, expected)
  end
end
