defmodule Cure.Stdlib.OtpCascadeExitTest do
  @moduledoc """
  `Std.Otp.CascadeExit` — cascading exit propagation along a link chain: `Cascade(before,
  after)` propagates an abnormal exit through `before`, killing non-trapping processes until
  the first trapping one absorbs it, leaving `after` alive. `run_cascade` proves the cascade
  is total. Re-checked every build via the stdlib preload; these tests pin the cutoff — the
  survivors are exactly the suffix from the first trapping process.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Trap = Trapping | NotTrapping
    type Chain = CNil | CCons(Trap, Chain)
    type Cascade indices (before: Chain, after: Chain)
      CascEmpty : Cascade(CNil, CNil)
      CascStop  : Cascade(CCons(Trapping, rest), CCons(Trapping, rest))
      CascProp  : Cascade(rest, after) -> Cascade(CCons(NotTrapping, rest), after)
    type CascadeOf indices (before: Chain)
      MkCascadeOf : (after: Chain) -> Cascade(before, after) -> CascadeOf(before)
    fn run_cascade(c: Chain) -> CascadeOf(c) = match c
      CNil()      -> MkCascadeOf(CNil, CascEmpty())
      CCons(t, r) -> match t
        Trapping    -> MkCascadeOf(CCons(Trapping, r), CascStop())
        NotTrapping -> match run_cascade(r)
          MkCascadeOf(after, casc) -> MkCascadeOf(after, CascProp(casc))
  """

  defp verdict(defs) do
    case Program.elaborate("mod CascT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a non-trapping head dies and the exit reaches the trapper, which survives" do
    # [NotTrapping, Trapping] cascades to [Trapping]: the first process dies, the trapper absorbs.
    defs = """
      fn ex() -> Cascade(CCons(NotTrapping, CCons(Trapping, CNil)), CCons(Trapping, CNil)) =
        CascProp(CascStop())
    """

    assert verdict(defs) == :accept
  end

  test "an all-non-trapping chain is fully annihilated (survivors empty)" do
    defs = """
      fn all_die() -> Cascade(CCons(NotTrapping, CCons(NotTrapping, CNil)), CNil) =
        CascProp(CascProp(CascEmpty()))
    """

    assert verdict(defs) == :accept
  end

  test "the trapping process cannot be reported dead (cutoff is the first trapper)" do
    # Claiming [NotTrapping, Trapping] cascades to CNil is false: CascProp needs the rest
    # (starting with Trapping) to cascade to CNil, but a trapping head only cascades to itself.
    defs = """
      fn bad() -> Cascade(CCons(NotTrapping, CCons(Trapping, CNil)), CNil) =
        CascProp(CascStop())
    """

    assert verdict(defs) == :reject
  end
end
