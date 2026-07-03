defmodule Antigen.Assays.TotalityTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Totality, as: A
  alias Antigen.Generators.Totality, as: G

  test "does NOT flag the mutual pair now the certifier soundly rejects it" do
    # Post-fix, `totality/diverging`'s invariant ("kernel must NOT certify") is
    # satisfied — the certifier correctly refuses the mutual cycle — so the assay
    # reports no violation. (While the hole was live this returned a violation;
    # the never-pruned corpus antibody is the standing regression guard.)
    assert :ok == A.run(G.diverging_mutual_pair())
  end

  test "passes a genuinely terminating structural def (completeness direction)" do
    assert :ok == A.run(G.structural_terminating())
  end

  test "bool_elim totality-hole guard: a self-call hidden in a branch is NOT certified" do
    # Before certificate.ex's :bool_elim clauses, `calls?` missed the branch
    # self-call and this loop was wrongly certified total (soundness infection).
    assert :ok == A.run(G.diverging_bool_elim_branch())
  end

  test "bool_elim anti-over-correction: a decreasing self-call inside a branch still certifies" do
    assert :ok == A.run(G.terminating_bool_elim_branch())
  end

  # -- W1: the adversarial diverging set (pre-port banking spec §4 W1) --------
  # Every one must replay :ok — i.e. the certifier certifies NO focus member.
  # These are the Lee–Jones–Ben-Amram discriminators, banked BEFORE the P1
  # size-change port so the permissiveness transition is born inside the net.

  test "W1: 3-cycle f→g→h→f is not certified" do
    assert :ok == A.run(G.diverging_three_cycle())
  end

  test "W1: cycle mediated through a total helper is not certified" do
    assert :ok == A.run(G.diverging_mediated_cycle())
  end

  test "W1: the total mediator itself still certifies (non-cyclic subroutine)" do
    c = G.diverging_mediated_cycle()
    env = G.env_of(c)

    assert Cure.Core.Certificate.terminating?(
             :total_id,
             Cure.Core.Env.get_def(env, :total_id).body,
             env
           )
  end

  test "W1: argument-permuting size-preserving pair is not certified" do
    assert :ok == A.run(G.diverging_permuting_pair())
  end

  test "W1: constructor-regrowing self-call is not certified" do
    assert :ok == A.run(G.diverging_regrowing_self())
  end

  test "W1: one-leg-decreasing mutual pair is not certified" do
    assert :ok == A.run(G.diverging_one_leg_pair())
  end

  # -- W2: reach pins (pre-port banking spec §4 W2, D2/D3) --------------------
  # Labels state mathematical truth (:terminating — each IS well-founded); the
  # assertions pin today's CONSERVATIVE REJECTION. P1 (size-change) flips these
  # to :ok by migrating the banked records from reach.sexp into corpus.sexp —
  # at which point these assertions are updated to assert :ok in the same commit.

  test "W2 reach pin: even/odd structural mutual pair is conservatively rejected today" do
    assert {:violation, {:wrongly_rejected, [:even, :odd]}} ==
             A.run(G.wellfounded_even_odd())
  end

  test "W2 reach pin: Ackermann (lexicographic two-argument descent) is conservatively rejected today" do
    assert {:violation, {:wrongly_rejected, [:ack]}} == A.run(G.wellfounded_ackermann())
  end

  test "W2 reach pin: permuted well-founded pair is conservatively rejected today" do
    assert {:violation, {:wrongly_rejected, [:f, :g]}} ==
             A.run(G.wellfounded_permuted_pair())
  end
end
