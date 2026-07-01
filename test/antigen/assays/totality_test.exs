defmodule Antigen.Assays.TotalityTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Totality, as: A
  alias Antigen.Generators.Totality, as: G

  test "does NOT flag the mutual pair now the certifier soundly rejects it" do
    # Post-fix, `totality/diverging`'s invariant ("kernel must NOT certify") is
    # satisfied — the certifier correctly refuses the mutual cycle — so the assay
    # reports no violation. (While the hole was live this returned a violation;
    # the never-pruned corpus antibody is the standing regression guard.)
    assert :ok == A.run(G.diverging_mutual_pair())
  end

  test "passes a genuinely terminating structural def (completeness direction)" do
    assert :ok == A.run(G.structural_terminating())
  end
end
