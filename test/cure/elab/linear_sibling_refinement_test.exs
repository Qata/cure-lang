defmodule Cure.Elab.LinearSiblingRefinementTest do
  @moduledoc """
  A `with r` handler may match on `r` while a LINEAR sibling whose type depends on
  `r` (`cap : ReplyCap(r)`) is in scope, refine that sibling per branch, and consume
  it exactly once — the ergonomic OTP handler shape

      with r
        GetCount() -> reply(cap, R0)
        …

  Previously this over-rejected: `with`'s Eq-transport encodes the sibling as
  `transport_case(prf) applied to cap` (a collapsible case = identity on `cap`)
  which the relevance checker ω-scaled pre-erasure. The sibling refinement now uses
  MOTIVE-GENERALIZATION — `(case r of λcap'. body) cap`, a real λ binder per branch —
  and the relevance CONVOY rule counts the linear `cap` once. Linearity is still
  enforced: dropping or duplicating `cap` in a branch is rejected.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp verdict(defs) do
    src = """
    mod LinSib
      type Reply0 = R0
      type Reply1 = R1a | R1b
      type Req = GetCount | SetName(Reply0) | Ping
      fn ReplyOf(r: Req) -> Type = match r
        GetCount()  -> Reply0
        SetName(_)  -> Reply1
        Ping()      -> Reply1
      type ReplyCap(r: Req) indices ()
        MkCap : ReplyCap(r)
      type Replied = Done
      type Pair = MkPair(Replied, Replied)
      fn reply({r: Req}, cap :linear ReplyCap(r), v: ReplyOf(r)) -> Replied =
        match cap
          MkCap() -> Done
    #{defs}
    end
    """

    case Program.elaborate(src) do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "branching handler consuming the linear capability once per path is accepted" do
    defs = """
      fn handle(r: Req, cap :linear ReplyCap(r)) -> Replied = with r
        GetCount()  -> reply(cap, R0)
        SetName(_)  -> reply(cap, R1a)
        Ping()      -> reply(cap, R1b)
    """

    assert verdict(defs) == :accept
  end

  test "a branch that DROPS the linear capability is rejected" do
    defs = """
      fn handle(r: Req, cap :linear ReplyCap(r)) -> Replied = with r
        GetCount()  -> Done
        SetName(_)  -> reply(cap, R1a)
        Ping()      -> reply(cap, R1b)
    """

    assert verdict(defs) == :reject
  end

  test "a branch that DUPLICATES the linear capability is rejected" do
    defs = """
      fn handle(r: Req, cap :linear ReplyCap(r)) -> Pair = with r
        GetCount()  -> MkPair(reply(cap, R0), reply(cap, R0))
        SetName(_)  -> MkPair(reply(cap, R1a), Done)
        Ping()      -> MkPair(reply(cap, R1b), Done)
    """

    assert verdict(defs) == :reject
  end
end
