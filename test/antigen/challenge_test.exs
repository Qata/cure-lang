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

  test "indexed_case challenge round-trips through to_pieces/from_pieces" do
    dec = {:data, :Dec, [], []}
    fam = Cure.Core.Inductive.family(:Dec, [], [], 0)
    ctors = [Cure.Core.Inductive.ctor(:Dcoupled, [], []), Cure.Core.Inductive.ctor(:Causal, [], [])]

    payload = %{
      families: [{fam, ctors}],
      def_name: :probe,
      def_type: dec,
      def_body: {:case, {:ctor, :Causal, []}, {:lam, dec, dec},
                 [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}
    }

    c = Antigen.Challenge.new(kind: :indexed_case, assay: "indexed/case", label: :well_typed, payload: payload)
    {scaffold, pieces} = Antigen.Challenge.to_pieces(c)
    back = Antigen.Challenge.from_pieces(:indexed_case, "indexed/case", :well_typed, nil, nil, scaffold, pieces)

    assert back.kind == :indexed_case
    assert back.payload.def_name == :probe
    assert back.payload.def_type == dec
    assert back.payload.def_body == payload.def_body
    assert back.payload.families == [{fam, ctors}]
  end
end
