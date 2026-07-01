defmodule Antigen.Generators.RewriteTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Rewrite
  alias Cure.Core.Kernel

  defp checks?(c), do: Kernel.check_def(Rewrite.env_of(c), c.payload.def_name)

  test "4.1 eq_formation: well-typed accepted, ill-typed rejected, labels correct" do
    wt = Rewrite.eq_formation(:well_typed)
    it = Rewrite.eq_formation(:ill_typed)
    assert wt.label == :well_typed and it.label == :ill_typed
    assert wt.kind == :rewrite_eq and wt.assay == "rewrite/eq"
    assert :ok == checks?(wt)
    assert {:error, _} = checks?(it)
  end
end
