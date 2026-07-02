defmodule Antigen.Assays.TermTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Term, as: A
  alias Antigen.Challenge
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.Backend.StreamData, as: B

  defp samples(id, n), do: B.interp(Term.typed_term(id)) |> Enum.take(n)

  test "infer_check assay is green on generated well-typed terms" do
    for c <- samples("term/infer_check", 60), do: assert A.run(c) == :ok
  end

  test "subject_reduction assay is green on generated well-typed terms" do
    for c <- samples("term/subject_reduction", 60), do: assert A.run(c) == :ok
  end

  test "normalization assay is green on generated well-typed terms" do
    for c <- samples("term/normalization", 60), do: assert A.run(c) == :ok
  end

  test "a deliberately ill-typed :typed_term is caught (mechanism check)" do
    # hand-break the claim: term {:var,0} but empty context → infer fails
    bad = Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: SigMenu.nat(), term: {:var, 0}})
    assert {:violation, {:infer_failed, _}} = A.run(bad)
  end
end
