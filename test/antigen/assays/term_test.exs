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

  test "erasure_preservation assay is green on generated well-typed terms" do
    for c <- samples("term/erasure_preservation", 60), do: assert A.run(c) == :ok
  end

  # -- BANKED FINDING: Normalise non-idempotence on context-closing lambdas ----
  #
  # A frozen Pi-goal challenge (captured from the generator, ctx depth 4) on which
  # the trusted `Cure.Core.Normalise` is NON-IDEMPOTENT: nf(nf t) ≠ nf(t), the
  # normal form oscillating with period 2 (two context de Bruijn indices are
  # transposed on each renormalization). The `term/normalization` assay correctly
  # flags it. This is a REAL kernel (TCB) finding — the reach-expansion's Pi goals
  # surfaced it. Pi menu seeds are withheld (see SigMenu.goal_types/0) until it is
  # fixed; when the normalizer is corrected, THIS ASSERTION FLIPS to `:ok` — the
  # red-green target for the fix (same banking pattern as the erase/parse_model
  # findings). Report: docs/superpowers/reports/2026-07-04-antigen-nf-nonidempotence-finding.md
  test "banked finding: Normalise non-idempotence on a frozen Pi challenge (flips to :ok when kernel fixed)" do
    {payload, _} = Code.eval_file("test/antigen/fixtures/nf_oscillation_pi.exs")
    c = Challenge.new(kind: :typed_term, assay: "term/normalization", label: :well_typed, payload: payload)
    assert {:violation, {:not_idempotent, nf1, nf2}} = A.run(c)
    assert nf1 != nf2
    # confirm it is a genuine oscillation (period 2), not a one-shot divergence:
    # the original term IS well-typed (infer accepts it), so a sound normalizer
    # would be idempotent here.
    env = SigMenu.env_of(:v1)
    ctx = SigMenu.rebuild_context(env, payload.ctx)
    assert {:ok, _} = Cure.Core.Kernel.infer(ctx, payload.term)
    nf3 = Cure.Core.Normalise.nf(ctx, nf2, fuel: 500_000)
    assert nf3 == nf1, "expected period-2 oscillation (nf3 == nf1)"
  end

  test "a deliberately ill-typed :typed_term is caught (mechanism check)" do
    # hand-break the claim: term {:var,0} but empty context → infer fails
    bad = Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: SigMenu.nat(), term: {:var, 0}})
    assert {:violation, {:infer_failed, _}} = A.run(bad)
  end
end
