defmodule Antigen.Assays.KernelLawTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Term, as: TermGen
  alias Antigen.Runner

  test "typed_term/1 accepts the new kernel-law assay-ids (guard widened)" do
    for id <- ~w(kernel/shift_subst kernel/weakening kernel/confluence) do
      # returns a Gen.t() (a tagged tuple), not raising FunctionClauseError
      assert is_tuple(TermGen.typed_term(id))
    end
  end

  test "runner registry routes the three kernel-law ids to KernelLaw" do
    for id <- ~w(kernel/shift_subst kernel/weakening kernel/confluence) do
      assert Runner.assay_module_for(id) == Antigen.Assays.KernelLaw
    end
  end
end
