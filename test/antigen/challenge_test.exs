defmodule Antigen.ChallengeTest do
  use ExUnit.Case, async: true
  alias Antigen.Challenge

  test "a stub challenge holds a single Core term and defaults" do
    c = Challenge.stub({:type, 0})
    assert %Challenge{kind: :stub, assay: "stub", label: :none} = c
    assert c.payload == %{term: {:type, 0}}
    assert c.seed == nil
  end

  test "new/1 fills fields from a keyword list" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:var, 0}}, seed: 7)
    assert c.seed == 7
    assert c.payload.term == {:var, 0}
  end
end
