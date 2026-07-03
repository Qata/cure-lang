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
end
