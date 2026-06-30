defmodule Cure.Core.ConvTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Conv

  test "beta: (λ.#0) Type0 ≡ Type0" do
    assert Conv.conv?({:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}}, {:type, 0}, [], 0)
  end

  test "reflexivity of a lambda" do
    assert Conv.conv?({:lam, {:type, 0}, {:var, 0}}, {:lam, {:type, 0}, {:var, 0}}, [], 0)
  end

  test "eta: f ≡ λ. (f #0) at a function type" do
    # context: f is var 0 (a neutral). env binds it; depth = 1.
    env = [{:vneutral, {:nvar, 0}}]
    f = {:var, 0}
    eta = {:lam, {:type, 0}, {:app, {:var, 1}, {:var, 0}}}
    assert Conv.conv?(f, eta, env, 1)
    assert Conv.conv?(eta, f, env, 1)
  end

  test "negative: Type0 ≢ Type1" do
    refute Conv.conv?({:type, 0}, {:type, 1}, [], 0)
  end

  test "negative: distinct constructors are not convertible" do
    refute Conv.conv?({:ctor, :Dcoupled, []}, {:ctor, :Causal, []}, [], 0)
  end

  test "Pi types compare domain and codomain" do
    assert Conv.conv?({:pi, {:type, 0}, {:var, 0}}, {:pi, {:type, 0}, {:var, 0}}, [], 0)
    refute Conv.conv?({:pi, {:type, 0}, {:var, 0}}, {:pi, {:type, 1}, {:var, 0}}, [], 0)
  end
end
