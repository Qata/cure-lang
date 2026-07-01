defmodule Antigen.Generators.ForcingTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Forcing
  alias Antigen.Corpus
  alias Cure.Core.Env

  test "forcing_pair builds structurally-distinct terms t (headed by f) and t' (headed by g)" do
    c = Forcing.forcing_pair()
    assert c.kind == :forcing_pair and c.label == :diverging
    %{t: t, tprime: tp} = c.payload
    assert t != tp
    assert {:app, {:global, :f}, _} = t
    assert {:app, {:global, :g}, _} = tp
  end

  test "certified_env_of reproduces the hole: the diverging globals are wrongly certified" do
    c = Forcing.forcing_pair()
    env = Forcing.certified_env_of(c)
    assert Env.certified?(env, :f)
    assert Env.certified?(env, :g)
  end

  test "a :forcing_pair round-trips through the corpus with t/tprime intact" do
    c = Forcing.forcing_pair()
    line = Corpus.encode_record(c)
    assert {:ok, c2} = Corpus.decode_record(line)
    assert c2.payload.t == c.payload.t
    assert c2.payload.tprime == c.payload.tprime
  end
end
