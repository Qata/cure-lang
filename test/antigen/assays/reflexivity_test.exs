defmodule Antigen.Assays.ReflexivityTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Reflexivity, as: A
  alias Antigen.Generators.Forcing, as: G

  test "flags the forcing pair as non-normalizing (conv exceeds the fixed fuel)" do
    assert {:violation, {:non_normalizing, _}} = A.run(G.forcing_pair())
  end
end
