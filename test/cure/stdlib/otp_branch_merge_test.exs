defmodule Cure.Stdlib.OtpBranchMergeTest do
  @moduledoc """
  `Std.Otp.BranchMerge` — the multiparty branch-MERGE operator and choice projection coherence.
  A global protocol with CHOICE (`GCho`) projects onto a bystander via `merge`, which unions
  differing receives into an external choice. `merge_idem` (a type merges with itself — the
  identical-bystander base of coherence) and `choice_duality` (a coherent RA/RB protocol with
  choice projects its two active roles to DUAL LSel/LBra endpoints — bilateral_duality lifted to
  branching). Cross-checked against Idris (oracle `branch_merge`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.BranchMerge")
  end

  test "branch-merge: idempotence and choice projection coherence" do
    src = """
    mod BranchMergeLaw
      use Std.Otp.BranchMerge
      fn idem(l: Local) -> Equivalent(Local, merge(l, l), l) =
        merge_idem(l)
      fn coherent(g: Global, w: Coherent(g)) -> Equivalent(Local, project(g, RA()), dual(project(g, RB()))) =
        choice_duality(w)
      fn union_inst() -> Equivalent(Local, merge(LRecv(TA(), LEnd()), LRecv(TB(), LEnd())), LBra(TA(), LEnd(), TB(), LEnd())) =
        reflexive(LBra(TA(), LEnd(), TB(), LEnd()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
