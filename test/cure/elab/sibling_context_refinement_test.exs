defmodule Cure.Elab.SiblingContextRefinementTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "E1: indexed evidence refines a sibling value for nested coverage" do
    source = """
    mod E1
      type Tag = TA | TB
      type Behaviour = BNil | BSend(Tag, Behaviour) | BRecv(Tag, Behaviour)
      type SendsIn indices (b: Behaviour, t: Tag)
        SendHere  : SendsIn(BSend(t, k), t)
        SendSendK : SendsIn(k, t) -> SendsIn(BSend(y, k), t)
      fn witness_head(b: Behaviour, {t: Tag}, s: SendsIn(b, t)) -> Tag = match s
        SendHere()    -> match b
          BSend(y, k) -> y
          BNil()      -> impossible
          BRecv(y, k) -> impossible
        SendSendK(s2) -> match b
          BSend(y, k) -> y
          BNil()      -> impossible
          BRecv(y, k) -> impossible
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "E1/E2: an implication witness refines both sibling bits" do
    source = """
    mod ImpRefine
      type B = F | T
      type Imp indices (a: B, b: B)
        ImpFF : Imp(F, F)
        ImpFT : Imp(F, T)
        ImpTT : Imp(T, T)
      fn f(xa: B, ya: B, i: Imp(xa, ya)) -> B = match i
        ImpFF() -> xa
        ImpFT() -> ya
        ImpTT() -> xa
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
