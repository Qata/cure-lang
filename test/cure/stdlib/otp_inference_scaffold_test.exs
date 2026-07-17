defmodule Cure.Stdlib.OtpInferenceScaffoldTest do
  @moduledoc """
  The G9 research scaffolds (`docs/research/process-types/scaffolds/`) are DESIGN ARTIFACTS
  for the open core of mailbox-type inference: the least-fixpoint outer shape
  (`inference_fixpoint.cure`) and the constraint-generation frontier
  (`inference_frontier.cure`), with typed holes (`?name`) for the intractable inner parts.

  These tests pin that the OUTER SHAPES are well-formed — they type-check with their holes,
  so the interfaces the holes must satisfy are real, not hand-waving. The holes' fills are
  mapped to specific Lean mathlib / Lean-core theorems in
  `2026-07-17-mailbox-inference-fixpoint-shape.md`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @scaffold_dir "docs/research/process-types/scaffolds"

  defp elaborates?(file) do
    path = Path.join([File.cwd!(), @scaffold_dir, file])
    case Program.elaborate(File.read!(path)) do
      {:ok, _} -> true
      {:error, _} -> false
    end
  end

  test "the least-fixpoint inference scaffold type-checks with its holes" do
    assert elaborates?("inference_fixpoint.cure")
  end

  test "the constraint-generation frontier scaffold type-checks with its holes" do
    assert elaborates?("inference_frontier.cure")
  end

  test "the adequacy scaffold type-checks (preservation_at proved; adequacy/coverage holed)" do
    assert elaborates?("inference_adequacy.cure")
  end
end
