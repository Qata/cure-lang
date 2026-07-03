defmodule Antigen.Meta.SensitivityTest do
  @moduledoc "Run C sensitivity matrix: real kernel → sound; weakened kernel → the catalog cell."
  use ExUnit.Case, async: true
  alias Antigen.Meta.WeakKernel
  alias Antigen.Challenge

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  # -- Rows 2 & 3: Term term/infer_check --------------------------------------
  defp typed_term_ch,
    do:
      Challenge.new(
        kind: :typed_term,
        assay: "term/infer_check",
        label: :well_typed,
        payload: %{sig: :v1, ctx: [], type: @nat, term: @sz}
      )

  test "row 2 — infer_wrong_type is CAUGHT by term/infer_check" do
    ch = typed_term_ch()
    assert :ok = Antigen.Assays.Term.run(ch, WeakKernel.real())
    assert {:violation, {:check_disagrees, _}} =
             Antigen.Assays.Term.run(ch, WeakKernel.weaken(:infer_wrong_type))
  end

  test "row 3 — check_accepts_all SLIPS past term/infer_check (documented gap)" do
    ch = typed_term_ch()
    assert :ok = Antigen.Assays.Term.run(ch, WeakKernel.real())
    # a consistency assay only ever calls `check` on the correctly-inferred type,
    # where :ok is the RIGHT answer — so an accept-all `check` is invisible to it.
    assert :ok = Antigen.Assays.Term.run(ch, WeakKernel.weaken(:check_accepts_all))
  end

  # -- Row 4: Positivity ------------------------------------------------------
  test "row 4 — positive_accepts_all is CAUGHT by positivity (negative-label family)" do
    ch = Antigen.Generators.Positivity.negative_family()
    assert :ok = Antigen.Assays.Positivity.run(ch, WeakKernel.real())

    assert {:violation, {:wrongly_accepted, :Bad}} =
             Antigen.Assays.Positivity.run(ch, WeakKernel.weaken(:positive_accepts_all))
  end

  # -- Row 5: Universes -------------------------------------------------------
  test "row 5 — universe_accepts_all is CAUGHT by universes (Type-in-Type ill_typed def)" do
    ch = Antigen.Generators.Universes.type_in_type(:ill_typed)
    assert :ok = Antigen.Assays.Universes.run(ch, WeakKernel.real())

    assert {:violation, {:wrongly_accepted, :u}} =
             Antigen.Assays.Universes.run(ch, WeakKernel.weaken(:universe_accepts_all))
  end

  # -- Rows 7 & 8: Reflexivity ------------------------------------------------
  test "row 7 — conv_always_true SLIPS past reflexivity (verdict-blind by design)" do
    ch = Antigen.Generators.Forcing.forcing_pair()
    assert :ok = Antigen.Assays.Reflexivity.run(ch, WeakKernel.real())
    # reflexivity is a non-termination detector: `{:ok, _} -> :ok`. A wrong
    # *verdict* is out of its contract (that is stuck_elim_delta's job, row 6).
    assert :ok = Antigen.Assays.Reflexivity.run(ch, WeakKernel.weaken(:conv_always_true))
  end

  test "row 8 — conv_exhausts_fuel is CAUGHT by reflexivity (its actual contract: halting)" do
    ch = Antigen.Generators.Forcing.forcing_pair()
    assert :ok = Antigen.Assays.Reflexivity.run(ch, WeakKernel.real())

    assert {:violation, {:non_normalizing, _}} =
             Antigen.Assays.Reflexivity.run(ch, WeakKernel.weaken(:conv_exhausts_fuel))
  end

  # -- Row 6: StuckElimDelta --------------------------------------------------
  # A minimal negative :stuck_elim control — two DISTINCT closed normal forms
  # (Z ≠ S(Z)) the kernel must not equate. The sensitivity target is the assay's
  # verdict-vs-committed-label decision (a permissive conv breaks it regardless of
  # whether the δ-of-stuck-eliminator seam fires), so an empty env + already-normal
  # pair exercises that decision deterministically.
  defp neg_stuck_elim_ch,
    do:
      Challenge.new(
        kind: :stuck_elim,
        assay: "stuck_elim_delta",
        label: :negative,
        payload: %{defs: [], focus: [], t: @z, tprime: @sz}
      )

  test "row 6 — conv_always_true is CAUGHT by stuck_elim_delta (negative control)" do
    ch = neg_stuck_elim_ch()
    assert :ok = Antigen.Assays.StuckElimDelta.run(ch, WeakKernel.real())

    assert {:violation, {:unsound_verdict, %{expected: false, got: true}}} =
             Antigen.Assays.StuckElimDelta.run(ch, WeakKernel.weaken(:conv_always_true))
  end
end
