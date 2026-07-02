defmodule Cure.Core.StuckElimDeltaTest do
  @moduledoc """
  Characterises the δ-of-stuck-eliminator seam in `Cure.Core.Normalise`:
  when a neutral's spine head is a stuck eliminator (`ncase`/`nfst`/`nsnd`)
  whose TARGET is itself a certified-global application, whnf must δ-reduce the
  target and, if a constructor/pair emerges, fire the ι-rule and re-apply the
  spine — so `plus (plus (S Z) Z) Z` computes instead of freezing, and
  `fst (g x)` projects instead of freezing.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Inductive, Normalise}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}

  # plus a b = case a of Z => b | S k => S (plus k b)   (recursion on 1st arg)
  # de Bruijn at the case: a = var 1, b = var 0.
  defp plus_body do
    z_branch = {:Z, 0, {:var, 0}}
    # inside S-branch (arity 1): k = var 0, b = var 1
    s_branch = {:S, 1, s({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}
    {:lam, @nat, {:lam, @nat, {:case, {:var, 1}, {:lam, @nat, @nat}, [z_branch, s_branch]}}}
  end

  defp plus_type, do: {:pi, @nat, {:pi, @nat, @nat}}

  # g x = (x, S x) : Nat -> (Nat × Nat)
  defp g_body, do: {:lam, @nat, {:pair, {:var, 0}, s({:var, 0})}}
  defp g_type, do: {:pi, @nat, {:sigma, @nat, @nat}}

  defp env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, @nat}], [])
    ])
    |> Env.add_def(:plus, plus_type(), plus_body())
    |> Env.certify(:plus)
    |> Env.add_def(:g, g_type(), g_body())
    |> Env.certify(:g)
  end

  defp ctx, do: Context.empty(env())

  defp plus(a, b), do: {:app, {:app, {:global, :plus}, a}, b}

  test "nf reduces a case whose scrutinee is a stuck certified-global application" do
    # plus (plus (S Z) Z) Z = plus 1 0 = 1 = S Z
    term = plus(plus(s(@z), @z), @z)
    assert s(@z) == Normalise.nf(ctx(), term)
  end

  test "nf reduces fst over a stuck certified-global spine" do
    # fst (g Z) = Z
    term = {:fst, {:app, {:global, :g}, @z}}
    assert @z == Normalise.nf(ctx(), term)
  end

  test "nf reduces snd over a stuck certified-global spine" do
    # snd (g Z) = S Z
    term = {:snd, {:app, {:global, :g}, @z}}
    assert s(@z) == Normalise.nf(ctx(), term)
  end

  test "conv decides plus (plus (S Z) Z) Z ≡ S Z (true)" do
    assert Conv.conv?(plus(plus(s(@z), @z), @z), s(@z), [], 0, env())
  end

  test "conv keeps distinct stuck eliminators distinct (fst vs snd)" do
    fst_gz = {:fst, {:app, {:global, :g}, @z}}
    snd_gz = {:snd, {:app, {:global, :g}, @z}}
    refute Conv.conv?(fst_gz, snd_gz, [], 0, env())
  end

  test "delta: :none still leaves the stuck eliminator frozen" do
    term = plus(plus(s(@z), @z), @z)
    # With δ disabled the outer application head cannot unfold at all.
    assert {:app, {:app, {:global, :plus}, _}, _} = Normalise.whnf(ctx(), term, delta: :none)
  end
end
