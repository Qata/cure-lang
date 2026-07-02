defmodule Antigen.ReifySplitGapReachTest do
  @moduledoc """
  Reach pin for the `Quote.reify` `{:vdata}` signature-gap (must-eventually-accept).

  The indexed with-clause LHS re-match convoy (`elaborate_with_rematch`) is a
  NON-TCB fix that works around this gap; it is NOT the principled repair. The
  repair — prior art in Agda/Lean — is signature-aware `Quote.reify` that recovers
  the param/index split (a TCB change). This pin keeps that debt visible so
  "the oracle/Antigen suite passes" does not bury it.

  The pinned challenge is a WELL-FORMED, refl-inhabited proposition
  (`λx. Eq(Type, SNat(x), SNat(x))` as a `:case` motive) that Cure currently
  REJECTS (`:bad_motive`): `check_motive_wf`'s `infer_type_value_sort` reifies the
  `{:vdata}` Eq-endpoints and the split-collapse re-checks with `:arg_arity`. The
  value-recursion fix (defc6cb) closed the Π/Σ DOMAIN path; the Eq-ENDPOINT path
  still reifies.

  MIGRATION CONTRACT (mirrors `reach_pin_test`): the run that lands signature-aware
  reify makes this challenge replay `:ok`; this test then goes red, and that run
  must migrate the record to a `corpus.sexp` seed and delete this pin — in the
  same commit. Records are never edited in place.
  """
  use ExUnit.Case, async: false
  alias Antigen.{Corpus, Assays}
  alias Antigen.Generators.Indexed

  @reach "test/antigen/reach_reify_split.sexp"

  @pin Indexed.reify_eq_indexed_reach(:well_typed)

  # The DOCUMENTED current verdict: ground truth is :well_typed, but the kernel
  # wrongly rejects it (:bad_motive) because of the reify {:vdata} split-collapse.
  @pinned {:violation, {:wrongly_rejected, {:reify_eq, :bad_motive}}}

  test "reify {:vdata} signature-gap is banked as a must-eventually-accept reach pin" do
    Corpus.append(@reach, @pin, Corpus.dedup_key(@pin, :antibody))

    decoded = @reach |> Corpus.stream() |> Enum.map(fn {:ok, c} -> c end)
    assert length(decoded) == 1

    for c <- decoded do
      assert Assays.Indexed.run(c) == @pinned,
             "reify split-gap reach pin drifted from its documented verdict — if " <>
               "signature-aware reify has landed, migrate this record to corpus.sexp " <>
               "as a seed and delete this pin (see @moduledoc migration contract)"
    end
  end
end
