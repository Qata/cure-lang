defmodule Cure.Core.NormaliseTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Inductive, Kernel, Normalise}

  @dec {:data, :Dec, [], []}
  @dcoupled {:ctor, :Dcoupled, []}
  @causal {:ctor, :Causal, []}
  @dec_motive {:lam, @dec, @dec}

  defp base do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
  end

  defp id_type, do: {:pi, {:type, 1}, {:type, 1}}
  defp id_body, do: {:lam, {:type, 1}, {:var, 0}}

  test "beta normalizes applications" do
    term = {:app, {:lam, {:type, 1}, {:var, 0}}, {:type, 0}}
    assert {:type, 0} == Normalise.nf(Context.empty(), term)
  end

  test "constructor case reduces by iota" do
    branches = [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]
    term = {:case, @causal, @dec_motive, branches}

    assert @causal == Normalise.nf(Context.empty(base()), term)
  end

  test "certified globals unfold" do
    env =
      base()
      |> Env.add_def(:id, id_type(), id_body())
      |> Env.certify(:id)

    term = {:app, {:global, :id}, {:type, 0}}
    assert {:type, 0} == Normalise.nf(Context.empty(env), term)
  end

  test "uncertified globals stay opaque" do
    env = Env.add_def(base(), :id, id_type(), id_body())
    term = {:app, {:global, :id}, {:type, 0}}

    assert {:app, {:global, :id}, {:type, 0}} == Normalise.whnf(Context.empty(env), term)
  end

  test "delta can be disabled for certified globals" do
    env =
      base()
      |> Env.add_def(:id, id_type(), id_body())
      |> Env.certify(:id)

    assert {:global, :id} == Normalise.whnf(Context.empty(env), {:global, :id}, delta: :none)
  end

  test "stuck cases are preserved through value read-back" do
    ctx = Context.extend(Context.empty(base()), {:vdata, :Dec, []})
    branches = [{:Dcoupled, 0, @dcoupled}, {:Causal, 0, @causal}]
    term = {:case, {:var, 0}, @dec_motive, branches}

    assert {:case, {:var, 0}, _motive, ^branches} = Normalise.nf(ctx, term)
  end

  test "fuel exhaustion is deterministic for cyclic certified delta" do
    env =
      base()
      |> Env.add_def(:f, @dec, {:global, :f})
      |> Env.certify(:f)

    assert :fuel_exhausted == Normalise.whnf(Context.empty(env), {:global, :f}, fuel: 5)
  end

  defp step_env do
    body =
      {:lam, @dec,
       {:case, {:var, 0}, @dec_motive,
        [
          {:Dcoupled, 0, @dcoupled},
          {:Causal, 0, {:app, {:global, :step}, {:var, 0}}}
        ]}}

    base()
    |> Env.add_def(:step, {:pi, @dec, @dec}, body)
    |> Env.certify(:step)
  end

  test "recursive certified definitions under neutral scrutinees stay FOLDED (lazy unfolding)" do
    # Reference-faithful (Idris/Lean/Agda): unfolding a pattern-matching
    # definition whose scrutinee is a neutral only exposes a matcher that is
    # itself stuck — so the definition is kept FOLDED (opaque application),
    # NOT eagerly expanded into its internal `case`. This keeps normal forms
    # canonical (a stuck recursive call has ONE shape everywhere) and keeps
    # conversion terminating on open terms.
    ctx = Context.extend(Context.empty(step_env()), {:vdata, :Dec, []})
    term = {:app, {:global, :step}, {:var, 0}}

    assert {:app, {:global, :step}, {:var, 0}} == Normalise.whnf(ctx, term, fuel: 5)
    assert {:app, {:global, :step}, {:var, 0}} == Normalise.nf(ctx, term, fuel: 5)
  end

  test "certified recursive globals still ι-reduce under constructor scrutinees" do
    # Guard against over-freezing: lazy unfolding must still fire when the
    # scrutinee IS a constructor. step(Dcoupled) selects the Dcoupled branch.
    ctx = Context.empty(step_env())
    term = {:app, {:global, :step}, @dcoupled}

    assert @dcoupled == Normalise.nf(ctx, term, fuel: 5)
    assert @dcoupled == Normalise.whnf(ctx, term, fuel: 5)
  end

  test "Kernel.normalize delegates to the shared normalizer" do
    term = {:app, {:lam, {:type, 1}, {:var, 0}}, {:type, 0}}
    assert Normalise.nf(Context.empty(), term) == Kernel.normalize(Context.empty(), term)
  end
end
