defmodule Antigen.Assays.TotalityTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Totality, as: A
  alias Antigen.Generators.Totality, as: G

  test "flags the diverging mutual pair — the live mutual-recursion hole" do
    assert {:violation, {:wrongly_certified, names}} = A.run(G.diverging_mutual_pair())
    assert :f in names and :g in names
  end

  test "passes a genuinely terminating structural def (completeness direction)" do
    assert :ok == A.run(G.structural_terminating())
  end
end
