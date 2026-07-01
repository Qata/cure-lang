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

  # Task 7: the untrusted match + ctor-app elaborator must thread the actual
  # parameter through the motive and the ctor-app result type. The param count
  # (1) differs from the index count (2), so a params=[] bug (or a subst that
  # zips the 1-element result_params-prefix against the scrutinee's 2 indices)
  # misaligns and fails to elaborate.
  @src2 """
  mod M
    type Dec = Dcoupled | Causal
    type Tagged(a: Type) indices (x: Dec, y: Dec)
      wrap : a -> Tagged(a, Causal, Dcoupled)
    fn probe(t: Tagged(Dec, Causal, Dcoupled)) -> Dec =
      match t
        wrap(v) -> v
  """

  # All the `{:lam, dom, …}` domains of a nested lambda, outermost first.
  defp lam_domains({:lam, dom, body}), do: [dom | lam_domains(body)]
  defp lam_domains(_), do: []

  test "match motive carries the scrutinee's actual parameter (not [])" do
    assert {:ok, env} = Program.elaborate(@src2)

    # probe = λ(t). case t of … ; the motive is the case's third element.
    assert {:lam, _t_type, {:case, _scrut, motive, _branches}} =
             Cure.Core.Env.get_def(env, :probe).body

    # The motive abstracts index_arity(2) + 1 = 3 binders; its innermost (last)
    # domain is the scrutinee-binder type `D params̄ j̄`. Params must be the
    # actual scrutinee parameter (Dec), NOT [] — and the index slice is 2 wide.
    scrut_binder_type = motive |> lam_domains() |> List.last()
    assert {:data, :Tagged, params, indices} = scrut_binder_type
    assert length(params) == 1, "motive dropped the parameter: #{inspect(scrut_binder_type)}"
    assert length(indices) == 2
  end
end
