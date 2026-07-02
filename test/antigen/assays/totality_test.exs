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
end
