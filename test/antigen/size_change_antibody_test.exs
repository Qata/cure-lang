defmodule Antigen.SizeChangeAntibodyTest do
  @moduledoc """
  Size-change termination antibody (#14). Guards the size-change certification
  added to the TCB certificate (`Cure.Core.Certificate.terminating?/3`) on both
  sides of the LJB principle, using the totality assay (oracle = known label):

    * REACH (must-eventually-accept): single-function, multi-argument lexicographic
      recursion — Ackermann — where NO single fixed argument position decreases at
      every self-call. Rejected by the old fixed-position guard; certified now via
      the change-matrix closure + reconstruct-equal (the inner call's first arg
      `S m'` is a rebuilt constructor that reconstructs the matched pattern, so it
      is size-`:equal` to the parameter). If reconstruct-equal regressed, Ackermann
      would fail to certify and this antibody goes red.

    * CONTROL (must-reject): single-function, multi-argument non-total recursion —
      `loop a b = loop (S a) (S b)` — whose parameters are UNMATCHED, so no
      reconstruction exists to fire on. Every arc is `:unknown`, the sole idempotent
      loop lacks a `:smaller` diagonal, and the def is soundly rejected. If
      reconstruct-equal ever fired on an unmatched param (a soundness infection),
      this loop would be wrongly certified and this antibody goes red.

  Direct-assertion antibody (cf. `certify_hardening_antibody_test.exs`): the assay
  IS the oracle check — `:ok` iff the certifier's verdict matches the by-construction
  label.
  """
  use ExUnit.Case, async: true

  alias Antigen.Assays.Totality, as: Assay
  alias Antigen.Generators.Totality
  alias Cure.Core.{Certificate, Env}

  test "REACH: Ackermann (lexicographic, single-function) now certifies total" do
    challenge = Totality.wellfounded_ackermann()
    assert challenge.label == :terminating
    # :ok ⇒ the certifier certifies every focus def, i.e. the reach flipped.
    assert :ok == Assay.run(challenge),
           "Ackermann must certify total under size-change + reconstruct-equal"
  end

  test "CONTROL: loop a b = loop (S a) (S b) is rejected (non-total multi-arg)" do
    challenge = Totality.diverging_size_change_control()
    assert challenge.label == :diverging
    # :ok ⇒ the certifier certifies NONE of the focus defs, i.e. loop stays rejected.
    assert :ok == Assay.run(challenge),
           "the non-total multi-arg control must NOT be certified"
  end

  test "CONTROL is rejected precisely because reconstruct-equal does not fire on unmatched params" do
    # The parameters a, b are never matched, so `S a` / `S b` reconstruct no
    # tracked pattern form — every change-matrix arc is :unknown, giving an
    # all-unknown idempotent loop with no :smaller diagonal.
    env = Totality.env_of(Totality.diverging_size_change_control())
    %{body: body} = Env.get_def(env, :loop)
    refute Certificate.terminating?(:loop, body, env)
  end
end
